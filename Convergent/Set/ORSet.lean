/-
  ORSet - Observed-Remove Set

  A set that supports add and remove operations where add wins over
  concurrent remove. Each addition is tagged with a unique ID, and
  remove only affects observed tags (not future additions).

  This allows re-adding elements after removal, unlike TwoPSet.

  State: Maps each element to the list of unique tags that added it.
  An element is present if it has at least one tag.

  Operations:
  - Add: Insert element with a unique tag
  - Remove: Remove all observed tags for an element
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.UniqueId
import Std.Data.HashMap

namespace Convergent

/-- State: element → list of unique tags -/
structure ORSet (α : Type) [BEq α] [Hashable α] where
  elements : Std.HashMap α (List UniqueId)
  deriving Repr, Inhabited

/-- Operation: add with tag, or remove observed tags -/
inductive ORSetOp (α : Type) where
  | add (value : α) (tag : UniqueId)
  | remove (value : α) (observedTags : List UniqueId)
  deriving Repr

namespace ORSet

variable {α : Type} [BEq α] [Hashable α]

/-- Empty set -/
def empty : ORSet α := { elements := {} }

/-- Get the tags for an element -/
def getTags (os : ORSet α) (value : α) : List UniqueId :=
  os.elements.getD value []

/-- Check if an element is in the set (has at least one tag) -/
def contains (os : ORSet α) (value : α) : Bool :=
  match os.elements[value]? with
  | some tags => !tags.isEmpty
  | none => false

/-- Get all elements currently in the set -/
def toList (os : ORSet α) : List α :=
  os.elements.toList.filterMap fun (elem, tags) =>
    if tags.isEmpty then none else some elem

/-- Get the size of the set -/
def size (os : ORSet α) : Nat :=
  os.elements.fold (init := 0) fun acc _ tags =>
    if tags.isEmpty then acc else acc + 1

/-- Apply an operation -/
def apply (os : ORSet α) (op : ORSetOp α) : ORSet α :=
  match op with
  | .add value tag =>
    let currentTags := os.getTags value
    if currentTags.any (· == tag) then os
    else { elements := os.elements.insert value (tag :: currentTags) }
  | .remove value observedTags =>
    match os.elements[value]? with
    | none => os
    | some currentTags =>
      let remainingTags := currentTags.filter fun tag =>
        !observedTags.any (· == tag)
      if remainingTags.isEmpty then
        { elements := os.elements.erase value }
      else
        { elements := os.elements.insert value remainingTags }

/-- Create an add operation -/
def add (value : α) (tag : UniqueId) : ORSetOp α :=
  .add value tag

/-- Create a remove operation that removes all currently observed tags -/
def remove (os : ORSet α) (value : α) : ORSetOp α :=
  .remove value (os.getTags value)

/-- Merge two ORSets (union of all tags per element) -/
def merge (a b : ORSet α) : ORSet α :=
  let merged := a.elements.fold (init := b.elements) fun acc elem tagsA =>
    let tagsB := b.getTags elem
    let combined := tagsA.foldl (init := tagsB) fun tags tag =>
      if tags.any (· == tag) then tags else tag :: tags
    if combined.isEmpty then acc else acc.insert elem combined
  { elements := merged }

instance : CmRDT (ORSet α) (ORSetOp α) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (ORSet α) (ORSetOp α) (List α) where
  query := toList

instance [ToString α] : ToString (ORSet α) where
  toString os :=
    let elems := os.toList.map toString
    s!"ORSet(\{{", ".intercalate elems}})"

/-! ## Monadic Interface -/

/-- Add an element with a unique tag in the CRDT monad -/
def addM (value : α) (tag : UniqueId) : CRDTM (ORSet α) Unit :=
  applyM (add value tag)

/-- Remove an element with its observed tags in the CRDT monad -/
def removeWithTagsM (value : α) (observedTags : List UniqueId) : CRDTM (ORSet α) Unit :=
  applyM (ORSetOp.remove value observedTags)

end ORSet

end Convergent
