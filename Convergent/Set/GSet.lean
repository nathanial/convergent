/-
  GSet - Grow-only Set

  A set that only supports adding elements, never removing them.
  This is the simplest set CRDT - add operations trivially commute.

  Operations:
  - Add: Insert an element into the set
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Std.Data.HashSet

namespace Convergent

/-- State: a HashSet of unique elements (O(1) lookup) -/
structure GSet (α : Type) [BEq α] [Hashable α] where
  elements : Std.HashSet α
  deriving Repr, Inhabited

/-- Operation: add an element -/
structure GSetOp (α : Type) where
  value : α
  deriving BEq, Repr

namespace GSet

variable {α : Type} [BEq α] [Hashable α]

/-- Empty set -/
def empty : GSet α := { elements := {} }

/-- Check if an element is in the set -/
def contains (gs : GSet α) (value : α) : Bool :=
  gs.elements.contains value

/-- Get all elements as a list -/
def toList (gs : GSet α) : List α :=
  gs.elements.toList

/-- Get the size of the set -/
def size (gs : GSet α) : Nat :=
  gs.elements.size

/-- Apply an add operation -/
def apply (gs : GSet α) (op : GSetOp α) : GSet α :=
  { elements := gs.elements.insert op.value }

/-- Create an add operation -/
def add (value : α) : GSetOp α :=
  { value }

/-- Merge two GSets (union) -/
def merge (a b : GSet α) : GSet α :=
  { elements := b.elements.fold (init := a.elements) fun acc elem => acc.insert elem }

instance : CmRDT (GSet α) (GSetOp α) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (GSet α) (GSetOp α) (List α) where
  query := toList

instance [ToString α] : ToString (GSet α) where
  toString gs :=
    let elems := gs.toList.map toString
    s!"GSet(\{{", ".intercalate elems}})"

/-! ## Monadic Interface -/

/-- Add an element to the set in the CRDT monad -/
def addM (value : α) : CRDTM (GSet α) Unit :=
  applyM (add value)

end GSet

end Convergent
