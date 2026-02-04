/-
  Fugue - Text CRDT with Maximal Non-Interleaving

  A tree-based sequence CRDT that guarantees text insertions from different
  users at the same position won't interleave character-by-character.

  Based on: "The Art of the Fugue: Minimizing Interleaving in Collaborative
  Text Editing" (Weidner, Gentle, Kleppmann 2023)

  Each element is a node in a tree structure. Elements track their original
  left and right neighbors (origins) at insertion time. Conflict resolution
  uses these origins to maintain non-interleaving order.

  State: A tree of nodes, each with unique ID and origin pointers.
  Operations:
  - Insert: Insert value with parent, side, and origins
  - Delete: Mark element as tombstone
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.ReplicaId
import Std.Data.HashMap
import Std.Data.HashSet

namespace Convergent

/-- Unique identifier for a Fugue node -/
structure FugueId where
  replica : ReplicaId
  counter : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

namespace FugueId

instance : Ord FugueId where
  compare a b :=
    match compare a.replica.id b.replica.id with
    | .eq => compare a.counter b.counter
    | other => other

instance : LT FugueId where
  lt a b := compare a b == .lt

instance : LE FugueId where
  le a b := compare a b != .gt

instance (a b : FugueId) : Decidable (a < b) :=
  if h : compare a b == .lt then isTrue h else isFalse h

instance (a b : FugueId) : Decidable (a <= b) :=
  if h : compare a b != .gt then isTrue h else isFalse h

end FugueId

/-- Side of the parent (left or right child) -/
inductive FugueSide where
  | left
  | right
  deriving BEq, Repr, Inhabited, DecidableEq

/-- A node in the Fugue tree -/
structure FugueNode (α : Type) where
  id : FugueId
  value : Option α             -- None indicates tombstone
  parent : Option FugueId      -- None means child of virtual root
  side : FugueSide             -- Left or right child
  leftOrigin : Option FugueId  -- Original left neighbor at insertion
  rightOrigin : Option FugueId -- Original right neighbor at insertion
  deriving Repr, Inhabited, BEq

/-- Fugue CRDT state -/
structure Fugue (α : Type) where
  nodes : Std.HashMap FugueId (FugueNode α)
  deriving Repr, Inhabited

/-- Operations on Fugue -/
inductive FugueOp (α : Type) where
  /-- Insert a node with all metadata -/
  | insert (node : FugueNode α)
  /-- Delete element by ID (tombstone) -/
  | delete (id : FugueId)
  deriving Repr

namespace Fugue

variable {α : Type}

/-- Empty Fugue -/
def empty : Fugue α := { nodes := {} }

/-- Check if an ID exists in the Fugue -/
def containsId (fugue : Fugue α) (id : FugueId) : Bool :=
  fugue.nodes.contains id

/-- Get a node by ID -/
def getNode (fugue : Fugue α) (id : FugueId) : Option (FugueNode α) :=
  fugue.nodes[id]?

/-- Get all children of a node on a specific side -/
private def getChildren (fugue : Fugue α) (parentId : Option FugueId) (side : FugueSide)
    : List (FugueNode α) :=
  fugue.nodes.toList.filterMap fun (_, node) =>
    if node.parent == parentId && node.side == side then some node else none

/-- Compare two optional FugueIds for sibling sorting.
    For rightOrigin comparison, we want reverse order for right-side children. -/
private def compareRightOrigins (a b : Option FugueId) : Ordering :=
  match a, b with
  | none, none => .eq
  | none, some _ => .lt  -- No origin comes first
  | some _, none => .gt
  | some idA, some idB => compare idA idB

/-- Check if a node is a same-author continuation of its leftOrigin.
    Returns true if the node's author matches its leftOrigin's author. -/
private def isSameAuthorContinuation (node : FugueNode α) : Bool :=
  match node.leftOrigin with
  | none => false
  | some leftId => node.id.replica == leftId.replica

/-- Compare two nodes for sibling ordering.
    Priority: rightOrigin > same-author continuation > replica ID
    Same-author continuations come first (they're continuing their own text). -/
private def compareSiblings (a b : FugueNode α) (reverseRightOrigin : Bool) : Bool :=
  let rightOriginCmp := if reverseRightOrigin
    then compareRightOrigins b.rightOrigin a.rightOrigin
    else compareRightOrigins a.rightOrigin b.rightOrigin
  match rightOriginCmp with
  | .lt => true
  | .gt => false
  | .eq =>
    -- Same rightOrigin: prefer same-author continuations
    let aContinues := isSameAuthorContinuation a
    let bContinues := isSameAuthorContinuation b
    if aContinues && !bContinues then true
    else if !aContinues && bContinues then false
    else a.id < b.id  -- Final tiebreaker: replica ID

/-- Sort siblings by rightOrigin, then same-author continuation, then ID.
    For right-side children, later rightOrigins come first (reverse order).
    For left-side children, earlier rightOrigins come first.
    Same-author continuations take priority over different-author insertions. -/
private def sortSiblings (siblings : List (FugueNode α)) (side : FugueSide)
    : List (FugueNode α) :=
  let arr := siblings.toArray
  let sorted := match side with
    | .right => arr.qsort fun a b => compareSiblings a b true
    | .left => arr.qsort fun a b => compareSiblings a b false
  sorted.toList

/-- Traverse the tree in-order to get document ordering.
    For each node: left subtree, then node, then right subtree.
    Guard against parent cycles by tracking visited nodes. -/
partial def traverse (fugue : Fugue α) : List (FugueNode α) :=
  -- Visit a single node with proper in-order traversal, tracking visited IDs.
  let rec visitNode (node : FugueNode α) (visited : Std.HashSet FugueId)
      : List (FugueNode α) × Std.HashSet FugueId :=
    if visited.contains node.id then
      ([], visited)
    else
      let visited' := visited.insert node.id
      let leftChildren := sortSiblings (getChildren fugue (some node.id) .left) .left
      let rightChildren := sortSiblings (getChildren fugue (some node.id) .right) .right
      let (leftPart, visited'') :=
        leftChildren.foldl
          (init := ([], visited'))
          (fun (acc, vis) child =>
            let (part, vis') := visitNode child vis
            (acc ++ part, vis'))
      let (rightPart, visited''') :=
        rightChildren.foldl
          (init := ([], visited''))
          (fun (acc, vis) child =>
            let (part, vis') := visitNode child vis
            (acc ++ part, vis'))
      (leftPart ++ [node] ++ rightPart, visited''')
  -- Visit a list of nodes, threading the visited set.
  let visitNodes (nodes : List (FugueNode α)) (visited : Std.HashSet FugueId)
      : List (FugueNode α) × Std.HashSet FugueId :=
    nodes.foldl
      (init := ([], visited))
      (fun (acc, vis) node =>
        let (part, vis') := visitNode node vis
        (acc ++ part, vis'))

  -- Start from virtual root (parent = none)
  let rootLeftChildren := sortSiblings (getChildren fugue none .left) .left
  let rootRightChildren := sortSiblings (getChildren fugue none .right) .right

  -- Visit all root children
  let (leftPart, visited) := visitNodes rootLeftChildren {}
  let (rightPart, _) := visitNodes rootRightChildren visited
  leftPart ++ rightPart

/-- Get all visible values in document order -/
def toList (fugue : Fugue α) : List α :=
  fugue.traverse.filterMap fun node => node.value

/-- Get the length (visible elements only) -/
def length (fugue : Fugue α) : Nat :=
  fugue.toList.length

/-- Get value at visible index -/
def get (fugue : Fugue α) (index : Nat) : Option α :=
  fugue.toList[index]?

/-- Get ID at visible index -/
def getIdAt (fugue : Fugue α) (index : Nat) : Option FugueId :=
  let visible := fugue.traverse.filter fun node => node.value.isSome
  visible[index]?.map fun node => node.id

/-- Check if id1 is an ancestor of id2 by walking up parent pointers.
    Guard against parent cycles by tracking visited IDs. -/
partial def isAncestor (fugue : Fugue α) (ancestorId childId : FugueId) : Bool :=
  let rec go (currentId : FugueId) (visited : Std.HashSet FugueId) : Bool :=
    if visited.contains currentId then
      false
    else if ancestorId == currentId then
      true
    else
      match fugue.getNode currentId with
      | none => false
      | some node =>
        match node.parent with
        | none => false
        | some parentId => go parentId (visited.insert currentId)
  go childId {}

/-- Determine parent and side for a new insertion between leftOrigin and rightOrigin -/
def determineParentAndSide (fugue : Fugue α) (leftOrigin rightOrigin : Option FugueId)
    : Option FugueId × FugueSide :=
  match leftOrigin, rightOrigin with
  | none, none => (none, .right)           -- Empty document, first element
  | some left, none => (some left, .right) -- Append after left
  | none, some right => (some right, .left) -- Prepend before right
  | some left, some right =>
    -- Check if left is an ancestor of right
    if isAncestor fugue left right then
      (some right, .left)  -- Insert as left child of right
    else
      (some left, .right)  -- Insert as right child of left

/-- Apply an operation to the Fugue.
    Insert is idempotent: duplicate IDs are ignored (tombstone wins).
    Delete creates tombstone even for unknown IDs (for commutativity). -/
def apply (fugue : Fugue α) (op : FugueOp α) : Fugue α :=
  match op with
  | .insert node =>
    match fugue.nodes[node.id]? with
    | some existing =>
      -- ID exists - tombstone wins
      if existing.value.isNone then fugue
      else if node.value.isNone then
        { nodes := fugue.nodes.insert node.id { existing with value := none } }
      else fugue  -- Both have values, keep existing
    | none =>
      { nodes := fugue.nodes.insert node.id node }
  | .delete id =>
    match fugue.nodes[id]? with
    | some existing =>
      { nodes := fugue.nodes.insert id { existing with value := none } }
    | none =>
      -- Create tombstone for unknown ID (for commutativity)
      let tombstone : FugueNode α := {
        id := id
        value := none
        parent := none
        side := .right
        leftOrigin := none
        rightOrigin := none
      }
      { nodes := fugue.nodes.insert id tombstone }

/-- Create an insert operation -/
def insert (node : FugueNode α) : FugueOp α := .insert node

/-- Create a delete operation -/
def delete (id : FugueId) : FugueOp α := .delete id

/-- Compare two optional FugueIds for deterministic ordering -/
private def compareOptId (a b : Option FugueId) : Ordering :=
  match a, b with
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some idA, some idB => compare idA idB

/-- Compare two nodes for deterministic merge ordering.
    Uses node ID as final tie-breaker to ensure total ordering. -/
private def compareNodes (a b : FugueNode α) : Ordering :=
  match compareOptId a.parent b.parent with
  | .eq =>
    match compareSide a.side b.side with
    | .eq =>
      match compareOptId a.leftOrigin b.leftOrigin with
      | .eq =>
        match compareOptId a.rightOrigin b.rightOrigin with
        | .eq => compare a.id b.id  -- Use ID as final tie-breaker
        | other => other
      | other => other
    | other => other
  | other => other
where
  compareSide (a b : FugueSide) : Ordering :=
    if a == b then .eq
    else if a == .left then .lt
    else .gt

/-- Merge two Fugue states.
    Combines all nodes. For duplicates: tombstone wins, then deterministic order. -/
def merge (a b : Fugue α) : Fugue α :=
  let merged := a.nodes.fold (init := b.nodes) fun acc id nodeA =>
    match acc[id]? with
    | some nodeB =>
      -- Both have this ID - tombstone wins, else deterministic comparison
      let winner := if nodeA.value.isNone || nodeB.value.isNone then
        { nodeA with value := none }
      else if compareNodes nodeA nodeB != .gt then nodeA else nodeB
      acc.insert id winner
    | none => acc.insert id nodeA
  { nodes := merged }

/-- High-level insert at visible index. Returns the operation and new state. -/
def insertAt (fugue : Fugue α) (replica : ReplicaId) (index : Nat) (value : α)
    : FugueOp α × Fugue α :=
  let visible := fugue.traverse.filter fun node => node.value.isSome

  -- Get left and right neighbors at the insertion point
  let leftNeighbor := if index == 0 then none else visible[index - 1]?.map (·.id)
  let rightNeighbor := visible[index]?.map (·.id)

  -- Determine parent and side
  let (parent, side) := determineParentAndSide fugue leftNeighbor rightNeighbor

  -- Generate new ID (use max counter + 1 for this replica)
  let maxCounter := fugue.nodes.fold (init := 0) fun acc _ node =>
    if node.id.replica == replica then max acc node.id.counter else acc
  let newId := FugueId.mk replica (maxCounter + 1)

  let node : FugueNode α := {
    id := newId
    value := some value
    parent := parent
    side := side
    leftOrigin := leftNeighbor
    rightOrigin := rightNeighbor
  }

  let op := FugueOp.insert node
  let newFugue := apply fugue op
  (op, newFugue)

/-- High-level delete at visible index. Returns the operation if index is valid. -/
def deleteAt (fugue : Fugue α) (index : Nat) : Option (FugueOp α) :=
  match fugue.getIdAt index with
  | some id => some (.delete id)
  | none => none

instance : CmRDT (Fugue α) (FugueOp α) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (Fugue α) (FugueOp α) (List α) where
  query := toList

instance [ToString α] : ToString (Fugue α) where
  toString f :=
    let elems := f.toList.map toString
    s!"Fugue([{", ".intercalate elems}])"

/-! ## Monadic Interface -/

/-- Insert a node in the CRDT monad -/
def insertM (node : FugueNode α) : CRDTM (Fugue α) Unit :=
  applyM (S := Fugue α) (Op := FugueOp α) (Fugue.insert node)

/-- Delete an element by ID in the CRDT monad -/
def deleteM (id : FugueId) : CRDTM (Fugue α) Unit :=
  applyM (S := Fugue α) (Op := FugueOp α) (Fugue.delete id)

end Fugue

end Convergent
