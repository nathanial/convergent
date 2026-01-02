/-
  RGA - Replicated Growable Array

  A list/sequence CRDT that supports insert and delete operations.
  Each element has a unique ID, and insertions specify which element
  they come after. Deletions use tombstones.

  This is suitable for collaborative text editing and ordered lists.

  State: A list of nodes with (id, afterId, value), where None indicates deleted.
  Ordering is derived from the afterId links, with concurrent inserts ordered
  deterministically by their IDs.

  Operations:
  - Insert: Insert a value after a specified position (or at start)
  - Delete: Mark an element as deleted (tombstone)
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.UniqueId
import Std.Data.HashMap
import Std.Data.HashSet

namespace Convergent

/-- An element in the RGA with its unique ID, origin, and optional value (None = tombstone) -/
structure RGANode (α : Type) where
  id : UniqueId
  afterId : Option UniqueId
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

/-! ## Ordering -/

/-- Merge two optional afterIds deterministically, preferring known IDs. -/
private def mergeAfterId (a b : Option UniqueId) : Option UniqueId :=
  match a, b with
  | none, none => none
  | some id, none => some id
  | none, some id => some id
  | some idA, some idB => if idA > idB then some idA else some idB

/-- Compute a deterministic ordering of nodes based on afterId and id. -/
partial def orderNodes (nodes : List (RGANode α)) : List (RGANode α) :=
  let idSet : Std.HashSet UniqueId :=
    nodes.foldl (init := {}) fun acc node => acc.insert node.id
  let parentOf (node : RGANode α) : Option UniqueId :=
    match node.afterId with
    | none => none
    | some parent =>
      if idSet.contains parent then some parent else none
  let children : Std.HashMap (Option UniqueId) (List (RGANode α)) :=
    nodes.foldl (init := {}) fun acc node =>
      let key := parentOf node
      let current := acc.getD key []
      acc.insert key (node :: current)
  let sortByIdAsc (xs : List (RGANode α)) : List (RGANode α) :=
    let arr := xs.toArray.qsort fun a b => a.id < b.id
    arr.toList
  let rec visit (parent : Option UniqueId) : List (RGANode α) :=
    let siblings := sortByIdAsc (children.getD parent [])
    siblings.flatMap fun child => child :: visit (some child.id)
  visit none

/-- Apply an operation.
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
        -- Existing is tombstone, keep it (delete wins), but update origin if known
        let updated := { existingNode with afterId := mergeAfterId existingNode.afterId afterId }
        let newNodes := rga.nodes.map fun node =>
          if node.id == id then updated else node
        { nodes := orderNodes newNodes }
      | some existingVal =>
        -- Both are inserts - use value comparison as tie-breaker
        if compare value existingVal == .gt then
          let updated : RGANode α := { id, afterId, value := some value }
          let newNodes := rga.nodes.map fun node =>
            if node.id == id then updated else node
          { nodes := orderNodes newNodes }
        else
          rga
    | none =>
      let newNode : RGANode α := { id, afterId, value := some value }
      { nodes := orderNodes (newNode :: rga.nodes) }
  | .delete id =>
    if rga.containsId id then
      -- Mark existing node as tombstone
      let newNodes := rga.nodes.map fun node =>
        if node.id == id then { node with value := none }
        else node
      { nodes := orderNodes newNodes }
    else
      -- Create tombstone for ID that doesn't exist yet (for commutativity)
      let tombstone : RGANode α := { id, afterId := none, value := none }
      { nodes := orderNodes (tombstone :: rga.nodes) }

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
      let mergedAfter := mergeAfterId nA.afterId nB.afterId
      if nA.value.isNone || nB.value.isNone then
        some { id := nA.id, afterId := mergedAfter, value := none }
      else
        -- Both have values - pick deterministically by value comparison
        match compare nA.value nB.value with
        | .gt => some { nA with afterId := mergedAfter }
        | .lt => some { nB with afterId := mergedAfter }
        | .eq => some { nA with afterId := mergedAfter }
    | some n, none => some n
    | none, some n => some n
    | none, none => none
  { nodes := orderNodes mergedNodes }

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
