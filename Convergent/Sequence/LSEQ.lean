/-
  LSEQ - Adaptive Sequence CRDT

  A position-based sequence CRDT for collaborative editing. Uses exponential
  tree allocation with adaptive Boundary+ and Boundary- strategies for
  sub-linear identifier growth.

  Unlike RGA which uses linked references (insert after ID), LSEQ uses
  dense position identifiers - paths through an exponential tree where
  each level has base(depth) = 2^(4+depth) available positions.

  State: A list of (LSEQId, Option value) where None indicates deleted.
  Position IDs define total ordering via lexicographic comparison.

  Operations:
  - Insert: Insert a value with a given position ID
  - Delete: Mark an element as deleted (tombstone)
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.ReplicaId

namespace Convergent

/-- Allocation strategy for a depth level -/
inductive LSEQStrategy where
  | boundaryPlus   -- Allocate near upper bound (good for appending)
  | boundaryMinus  -- Allocate near lower bound (good for prepending)
  deriving BEq, Repr, Inhabited

/-- A single level in a position identifier.
    Contains the allocated position and the site that allocated it. -/
structure LSEQLevel where
  pos : Nat
  site : ReplicaId
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Position identifier: a list of levels defining total ordering.
    Paths through the exponential tree. -/
structure LSEQId where
  levels : List LSEQLevel
  deriving BEq, Repr, Inhabited

/-- An element in the LSEQ with its position ID and optional value -/
structure LSEQNode (α : Type) where
  id : LSEQId
  value : Option α
  deriving Repr, Inhabited, BEq

/-- LSEQ state: list of nodes sorted by position ID -/
structure LSEQ (α : Type) where
  nodes : List (LSEQNode α)
  deriving Repr, Inhabited

/-- Operation: insert with position ID or delete by ID -/
inductive LSEQOp (α : Type) where
  /-- Insert value with a given position ID -/
  | insert (id : LSEQId) (value : α)
  /-- Delete the element with given ID -/
  | delete (id : LSEQId)
  deriving Repr

namespace LSEQLevel

instance : Ord LSEQLevel where
  compare a b :=
    match compare a.pos b.pos with
    | .eq => compare a.site b.site
    | other => other

instance : LT LSEQLevel where
  lt a b := compare a b == .lt

instance : LE LSEQLevel where
  le a b := compare a b != .gt

instance (a b : LSEQLevel) : Decidable (a < b) :=
  if h : compare a b == .lt then isTrue h else isFalse h

instance (a b : LSEQLevel) : Decidable (a <= b) :=
  if h : compare a b != .gt then isTrue h else isFalse h

end LSEQLevel

namespace LSEQId

/-- Compare two position IDs lexicographically -/
private def compareLevels : List LSEQLevel → List LSEQLevel → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt  -- Shorter prefix comes first
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match compare x y with
    | .eq => compareLevels xs ys
    | other => other

instance : Ord LSEQId where
  compare a b := compareLevels a.levels b.levels

instance : LT LSEQId where
  lt a b := compare a b == .lt

instance : LE LSEQId where
  le a b := compare a b != .gt

instance (a b : LSEQId) : Decidable (a < b) :=
  if h : compare a b == .lt then isTrue h else isFalse h

instance (a b : LSEQId) : Decidable (a <= b) :=
  if h : compare a b != .gt then isTrue h else isFalse h

instance : DecidableEq LSEQId := fun a b =>
  if h : a.levels = b.levels then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by intro heq; cases heq; contradiction)

/-- Create an ID with a single level -/
def single (pos : Nat) (site : ReplicaId) : LSEQId :=
  { levels := [{ pos, site }] }

/-- Append a level to an ID -/
def append (id : LSEQId) (level : LSEQLevel) : LSEQId :=
  { levels := id.levels ++ [level] }

/-- Get the position at a specific depth, with default for out of bounds -/
def getPosAt (id : LSEQId) (depth : Nat) (default : Nat) : Nat :=
  match id.levels[depth]? with
  | some level => level.pos
  | none => default

/-- Get the level at a specific depth -/
def getLevelAt (id : LSEQId) (depth : Nat) : Option LSEQLevel :=
  id.levels[depth]?

/-- Get prefix of ID up to (but not including) depth -/
def prefixTo (id : LSEQId) (depth : Nat) : LSEQId :=
  { levels := id.levels.take depth }

end LSEQId

namespace LSEQ

variable {α : Type}

/-- Empty LSEQ -/
def empty : LSEQ α := { nodes := [] }

/-- Calculate base for a given depth: 2^(4 + depth)
    depth 0: base = 16
    depth 1: base = 32
    depth 2: base = 64, etc. -/
def base (depth : Nat) : Nat := 2 ^ (4 + depth)

/-- Get allocation strategy for a (replica, depth) pair.
    Uses XOR for deterministic pseudo-random selection. -/
def getStrategy (replica : ReplicaId) (depth : Nat) : LSEQStrategy :=
  if (replica.id ^^^ depth) % 2 == 0 then .boundaryPlus else .boundaryMinus

/-- Allocate a position between lower and upper bounds.
    Returns a new unique position ID. -/
partial def allocateBetween (replica : ReplicaId) (lower upper : Option LSEQId) : LSEQId :=
  allocateAtDepth replica lower upper 0 []
where
  /-- Recursive helper: allocate at a specific depth -/
  allocateAtDepth (replica : ReplicaId) (lower upper : Option LSEQId)
      (depth : Nat) (prefix_ : List LSEQLevel) : LSEQId :=
    let baseVal := base depth
    let lowerPos := match lower with
      | none => 0
      | some id => id.getPosAt depth 0
    let upperPos := match upper with
      | none => baseVal
      | some id => id.getPosAt depth baseVal

    -- Check if there's space at this depth
    let interval := upperPos - lowerPos
    if interval > 1 then
      -- Space available: allocate within interval using strategy
      let strategy := getStrategy replica depth
      let newPos := match strategy with
        | .boundaryPlus => upperPos - 1  -- Near upper bound
        | .boundaryMinus => lowerPos + 1  -- Near lower bound
      let newLevel : LSEQLevel := { pos := newPos, site := replica }
      { levels := prefix_ ++ [newLevel] }
    else
      -- No space: descend to next depth, preserving the lower-bound level when available
      let currentLevel : LSEQLevel :=
        match lower with
        | some id =>
          match id.getLevelAt depth with
          | some level => level
          | none => { pos := lowerPos, site := replica }
        | none =>
          match upper with
          | some id =>
            match id.getLevelAt depth with
            | some level => { pos := lowerPos, site := level.site }
            | none => { pos := lowerPos, site := replica }
          | none => { pos := lowerPos, site := replica }
      -- Keep the lower/upper bounds - getPosAt will return defaults for missing levels
      allocateAtDepth replica lower upper (depth + 1) (prefix_ ++ [currentLevel])

/-- Insert a node maintaining sorted order by ID -/
private def insertSorted (nodes : List (LSEQNode α)) (node : LSEQNode α)
    : List (LSEQNode α) :=
  match nodes with
  | [] => [node]
  | n :: ns =>
    if compare node.id n.id == .lt then node :: n :: ns
    else n :: insertSorted ns node

/-- Get all visible values (excluding tombstones) in order -/
def toList (lseq : LSEQ α) : List α :=
  lseq.nodes.filterMap (·.value)

/-- Get the value at a visible index (0-based, excludes tombstones) -/
def get (lseq : LSEQ α) (index : Nat) : Option α :=
  lseq.toList[index]?

/-- Get the length (visible elements only) -/
def length (lseq : LSEQ α) : Nat :=
  lseq.toList.length

/-- Check if an ID exists in the LSEQ -/
def containsId (lseq : LSEQ α) (id : LSEQId) : Bool :=
  lseq.nodes.any (·.id == id)

/-- Get the ID at a visible index -/
def getIdAt (lseq : LSEQ α) (index : Nat) : Option LSEQId :=
  let visible := lseq.nodes.filter (·.value.isSome)
  visible[index]?.map (·.id)

/-- Insert a value at a visible index.
    Returns the operation to broadcast and the updated local state. -/
def insertAt (lseq : LSEQ α) (replica : ReplicaId) (index : Nat) (value : α)
    : LSEQOp α × LSEQ α :=
  let visible := lseq.nodes.filter (·.value.isSome)
  -- Find neighbors
  let lower := if index == 0 then none else visible[index - 1]?.map (·.id)
  let upper := visible[index]?.map (·.id)
  -- Allocate position
  let newId := allocateBetween replica lower upper
  let op := LSEQOp.insert newId value
  let node : LSEQNode α := { id := newId, value := some value }
  let newNodes := insertSorted lseq.nodes node
  (op, { nodes := newNodes })

/-- Apply an operation to state -/
def apply [Ord α] (lseq : LSEQ α) (op : LSEQOp α) : LSEQ α :=
  match op with
  | .insert id value =>
    -- Check if ID already exists
    match lseq.nodes.find? (·.id == id) with
    | some existingNode =>
      -- ID exists - check if we should update
      match existingNode.value with
      | none =>
        -- Existing is tombstone, keep it (delete wins)
        lseq
      | some existingVal =>
        -- Both are inserts - use value comparison as tie-breaker
        if compare value existingVal == .gt then
          let newNodes := lseq.nodes.map fun node =>
            if node.id == id then { node with value := some value }
            else node
          { nodes := newNodes }
        else
          lseq
    | none =>
      let node : LSEQNode α := { id, value := some value }
      let newNodes := insertSorted lseq.nodes node
      { nodes := newNodes }
  | .delete id =>
    if lseq.containsId id then
      -- Mark existing node as tombstone
      let newNodes := lseq.nodes.map fun node =>
        if node.id == id then { node with value := none }
        else node
      { nodes := newNodes }
    else
      -- Create tombstone for ID that doesn't exist yet (for commutativity)
      let tombstone : LSEQNode α := { id, value := none }
      let newNodes := insertSorted lseq.nodes tombstone
      { nodes := newNodes }

/-- Create an insert operation -/
def insert (id : LSEQId) (value : α) : LSEQOp α :=
  .insert id value

/-- Create a delete operation -/
def delete (id : LSEQId) : LSEQOp α :=
  .delete id

/-- Delete element at visible index -/
def deleteAt (lseq : LSEQ α) (index : Nat) : Option (LSEQOp α) :=
  match getIdAt lseq index with
  | some id => some (.delete id)
  | none => none

/-- Merge two LSEQ states.
    Combines all nodes, with tombstones taking precedence. -/
def merge [Ord α] (a b : LSEQ α) : LSEQ α :=
  -- Collect all unique IDs from both
  let aIds := a.nodes.map (·.id)
  let bIds := b.nodes.map (·.id)
  let allIds := (aIds ++ bIds).foldl (init := []) fun acc id =>
    if acc.any (· == id) then acc else id :: acc
  -- For each ID, merge the nodes
  let mergedNodes := allIds.filterMap fun id =>
    let inA := a.nodes.find? fun n => n.id == id
    let inB := b.nodes.find? fun n => n.id == id
    match inA, inB with
    | some nA, some nB =>
      -- Both have this ID - tombstone wins, otherwise pick deterministically
      if nA.value.isNone || nB.value.isNone then
        some { nA with value := none }
      else
        -- Both have values - pick deterministically by value comparison
        match compare nA.value nB.value with
        | .gt => some nA
        | .lt => some nB
        | .eq => some nA
    | some n, none => some n
    | none, some n => some n
    | none, none => none
  -- Sort by ID to maintain consistent ordering
  let sorted := mergedNodes.toArray.qsort fun x y => compare x.id y.id == .lt
  { nodes := sorted.toList }

instance [Ord α] : CmRDT (LSEQ α) (LSEQOp α) where
  empty := empty
  apply := apply
  merge := merge

instance [Ord α] : CmRDTQuery (LSEQ α) (LSEQOp α) (List α) where
  query := toList

instance [ToString α] : ToString (LSEQ α) where
  toString lseq :=
    let elems := lseq.toList.map toString
    s!"LSEQ([{", ".intercalate elems}])"

/-! ## Monadic Interface -/

/-- Insert a value with a position ID in the CRDT monad -/
def insertM [Ord α] (id : LSEQId) (value : α) : CRDTM (LSEQ α) Unit :=
  applyM (S := LSEQ α) (Op := LSEQOp α) (insert id value)

/-- Delete an element by ID in the CRDT monad -/
def deleteM [Ord α] (id : LSEQId) : CRDTM (LSEQ α) Unit :=
  applyM (S := LSEQ α) (Op := LSEQOp α) (delete id)

end LSEQ

end Convergent
