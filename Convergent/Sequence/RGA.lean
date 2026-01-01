/-
  RGA - Replicated Growable Array

  A list/sequence CRDT that supports insert and delete operations.
  Each element has a unique ID, and insertions specify which element
  they come after. Deletions use tombstones.

  This is suitable for collaborative text editing and ordered lists.

  State: A list of (UniqueId, Option value) where None indicates deleted.
  The list maintains insertion order based on the unique IDs.

  Operations:
  - Insert: Insert a value after a specified position (or at start)
  - Delete: Mark an element as deleted (tombstone)
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.UniqueId

namespace Convergent

/-- An element in the RGA with its unique ID and optional value (None = tombstone) -/
structure RGANode (α : Type) where
  id : UniqueId
  value : Option α
  deriving Repr, Inhabited, BEq

/-- State: list of nodes maintaining causal order -/
structure RGA (α : Type) where
  nodes : List (RGANode α)
  deriving Repr, Inhabited

/-- Operation: insert after a position or delete -/
inductive RGAOp (α : Type) where
  /-- Insert value after the element with given ID (None = insert at start) -/
  | insert (afterId : Option UniqueId) (value : α) (id : UniqueId)
  /-- Delete the element with given ID -/
  | delete (id : UniqueId)
  deriving Repr

namespace RGA

variable {α : Type}

/-- Empty RGA -/
def empty : RGA α := { nodes := [] }

/-- Find the index of a node by its ID -/
private def findIndex (nodes : List (RGANode α)) (id : UniqueId) : Option Nat :=
  nodes.findIdx? fun node => node.id == id

/-- Get all visible values (excluding tombstones) -/
def toList (rga : RGA α) : List α :=
  rga.nodes.filterMap fun node => node.value

/-- Get the value at a visible index (0-based, excludes tombstones) -/
def get (rga : RGA α) (index : Nat) : Option α :=
  rga.toList[index]?

/-- Get the length (visible elements only) -/
def length (rga : RGA α) : Nat :=
  rga.toList.length

/-- Check if an ID exists in the RGA -/
def containsId (rga : RGA α) (id : UniqueId) : Bool :=
  rga.nodes.any fun node => node.id == id

/-- Get the ID at a visible index -/
def getIdAt (rga : RGA α) (index : Nat) : Option UniqueId :=
  let visible := rga.nodes.filter fun node => node.value.isSome
  visible[index]? |>.map fun node => node.id

/-- Insert a new node after the specified ID.
    If afterId is None, insert at the start.
    For concurrent inserts at the same position, use ID ordering. -/
private def insertAfter (nodes : List (RGANode α)) (afterId : Option UniqueId)
    (newNode : RGANode α) : List (RGANode α) :=
  match afterId with
  | none =>
    -- Insert at start, but after any concurrent inserts with higher IDs
    let rec splitByHigherId (acc : List (RGANode α)) (rest : List (RGANode α)) : List (RGANode α) × List (RGANode α) :=
      match rest with
      | [] => (acc.reverse, [])
      | node :: rest' =>
        if node.id > newNode.id then splitByHigherId (node :: acc) rest'
        else (acc.reverse, rest)
    let (higher, lower) := splitByHigherId [] nodes
    higher ++ [newNode] ++ lower
  | some targetId =>
    -- Find the target and insert after it
    let rec go (acc : List (RGANode α)) (remaining : List (RGANode α)) : List (RGANode α) :=
      match remaining with
      | [] => acc.reverse ++ [newNode]  -- Target not found, append at end
      | node :: rest =>
        if node.id == targetId then
          -- Found target, now find correct position among concurrent inserts
          let rec findPos (prefix_ : List (RGANode α)) (suffix : List (RGANode α)) : List (RGANode α) :=
            match suffix with
            | [] => acc.reverse ++ [node] ++ prefix_.reverse ++ [newNode]
            | n :: ns =>
              if n.id > newNode.id then findPos (n :: prefix_) ns
              else acc.reverse ++ [node] ++ prefix_.reverse ++ [newNode] ++ suffix
          findPos [] rest
        else
          go (node :: acc) rest
    go [] nodes

/-- Apply an operation.
    Maintains ID-sorted order for CRDT law compliance.
    For commutativity:
    - Delete creates tombstone even if ID doesn't exist yet
    - Insert with existing ID uses value comparison as tie-breaker -/
def apply [Ord α] (rga : RGA α) (op : RGAOp α) : RGA α :=
  match op with
  | .insert afterId value id =>
    match rga.nodes.find? (·.id == id) with
    | some existingNode =>
      -- ID exists - check if we should replace (for commutativity with duplicate inserts)
      match existingNode.value with
      | none =>
        -- Existing is tombstone, keep it (delete wins)
        rga
      | some existingVal =>
        -- Both are inserts - use value comparison as tie-breaker
        if compare value existingVal == .gt then
          let newNodes := rga.nodes.map fun node =>
            if node.id == id then { node with value := some value }
            else node
          { nodes := newNodes }
        else
          rga
    | none =>
      let newNode : RGANode α := { id, value := some value }
      let inserted := insertAfter rga.nodes afterId newNode
      -- Sort by ID to maintain consistent ordering for CRDT laws
      let sorted := inserted.toArray.qsort fun a b => a.id < b.id
      { nodes := sorted.toList }
  | .delete id =>
    if rga.containsId id then
      -- Mark existing node as tombstone
      let newNodes := rga.nodes.map fun node =>
        if node.id == id then { node with value := none }
        else node
      { nodes := newNodes }
    else
      -- Create tombstone for ID that doesn't exist yet (for commutativity)
      let tombstone : RGANode α := { id, value := none }
      let sorted := (tombstone :: rga.nodes).toArray.qsort fun a b => a.id < b.id
      { nodes := sorted.toList }

/-- Create an insert operation -/
def insert (afterId : Option UniqueId) (value : α) (id : UniqueId) : RGAOp α :=
  .insert afterId value id

/-- Create a delete operation -/
def delete (id : UniqueId) : RGAOp α :=
  .delete id

/-- Merge two RGAs (state-based merge).
    Combines all nodes, with tombstones taking precedence.
    Uses deterministic ordering for commutativity. -/
def merge [Ord α] (a b : RGA α) : RGA α :=
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
  let sorted := mergedNodes.toArray.qsort fun a b => a.id < b.id
  { nodes := sorted.toList }

instance [Ord α] : CmRDT (RGA α) (RGAOp α) where
  empty := empty
  apply := apply
  merge := merge

instance [Ord α] : CmRDTQuery (RGA α) (RGAOp α) (List α) where
  query := toList

instance [ToString α] : ToString (RGA α) where
  toString rga :=
    let elems := rga.toList.map toString
    s!"RGA([{", ".intercalate elems}])"

/-! ## Monadic Interface -/

/-- Insert a value after a position in the CRDT monad -/
def insertM [Ord α] (afterId : Option UniqueId) (value : α) (id : UniqueId) : CRDTM (RGA α) Unit :=
  applyM (S := RGA α) (Op := RGAOp α) (insert afterId value id)

/-- Delete an element by ID in the CRDT monad -/
def deleteM [Ord α] (id : UniqueId) : CRDTM (RGA α) Unit :=
  applyM (S := RGA α) (Op := RGAOp α) (delete id)

end RGA

end Convergent
