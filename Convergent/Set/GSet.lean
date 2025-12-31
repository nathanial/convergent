/-
  GSet - Grow-only Set

  A set that only supports adding elements, never removing them.
  This is the simplest set CRDT - add operations trivially commute.

  Operations:
  - Add: Insert an element into the set
-/
import Convergent.Core.CmRDT

namespace Convergent

/-- State: a list of unique elements -/
structure GSet (α : Type) [BEq α] where
  elements : List α
  deriving Repr, Inhabited

/-- Operation: add an element -/
structure GSetOp (α : Type) where
  value : α
  deriving BEq, Repr

namespace GSet

variable {α : Type} [BEq α]

/-- Empty set -/
def empty : GSet α := { elements := [] }

/-- Check if an element is in the set -/
def contains (gs : GSet α) (value : α) : Bool :=
  gs.elements.any (· == value)

/-- Get all elements as a list -/
def toList (gs : GSet α) : List α :=
  gs.elements

/-- Get the size of the set -/
def size (gs : GSet α) : Nat :=
  gs.elements.length

/-- Apply an add operation -/
def apply (gs : GSet α) (op : GSetOp α) : GSet α :=
  if gs.contains op.value then gs
  else { elements := op.value :: gs.elements }

/-- Create an add operation -/
def add (value : α) : GSetOp α :=
  { value }

/-- Merge two GSets (union) -/
def merge (a b : GSet α) : GSet α :=
  let combined := b.elements.foldl (init := a.elements) fun acc elem =>
    if acc.any (· == elem) then acc else elem :: acc
  { elements := combined }

instance : CmRDT (GSet α) (GSetOp α) where
  empty := empty
  apply := apply

instance [ToString α] : ToString (GSet α) where
  toString gs :=
    let elems := gs.elements.map toString
    s!"GSet(\{{", ".intercalate elems}})"

end GSet

end Convergent
