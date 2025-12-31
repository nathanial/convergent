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

/-- Apply an operation -/
def apply (rga : RGA α) (op : RGAOp α) : RGA α :=
  match op with
  | .insert afterId value id =>
    if rga.containsId id then
      -- Duplicate operation, ignore
      rga
    else
      let newNode : RGANode α := { id, value := some value }
      { nodes := insertAfter rga.nodes afterId newNode }
  | .delete id =>
    let newNodes := rga.nodes.map fun node =>
      if node.id == id then { node with value := none }
      else node
    { nodes := newNodes }

/-- Create an insert operation -/
def insert (afterId : Option UniqueId) (value : α) (id : UniqueId) : RGAOp α :=
  .insert afterId value id

/-- Create a delete operation -/
def delete (id : UniqueId) : RGAOp α :=
  .delete id

/-- Merge two RGAs by replaying all unique operations -/
def merge (a b : RGA α) : RGA α :=
  -- Collect all unique nodes from both
  let allNodes := a.nodes ++ b.nodes.filter fun bNode =>
    !a.nodes.any fun aNode => aNode.id == bNode.id
  -- Merge tombstones: if either has deleted, it's deleted
  let mergedNodes := allNodes.map fun node =>
    let inA := a.nodes.find? fun n => n.id == node.id
    let inB := b.nodes.find? fun n => n.id == node.id
    match inA, inB with
    | some nA, some nB =>
      if nA.value.isNone || nB.value.isNone then
        { node with value := none }
      else node
    | _, _ => node
  -- Sort by ID to maintain consistent ordering
  let sorted := mergedNodes.toArray.qsort fun a b => a.id < b.id
  { nodes := sorted.toList }

instance : CmRDT (RGA α) (RGAOp α) where
  empty := empty
  apply := apply

instance [ToString α] : ToString (RGA α) where
  toString rga :=
    let elems := rga.toList.map toString
    s!"RGA([{", ".intercalate elems}])"

end RGA

end Convergent
