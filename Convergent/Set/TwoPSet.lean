/-
  TwoPSet - Two-Phase Set

  A set that supports both add and remove operations, with the constraint
  that once an element is removed, it cannot be re-added.

  This is implemented as two GSets:
  - added: elements that have been added
  - removed: elements that have been removed (tombstones)

  An element is in the set if it's in 'added' but not in 'removed'.

  Operations:
  - Add: Insert an element
  - Remove: Mark an element as removed (tombstone)
-/
import Convergent.Core.CmRDT
import Convergent.Set.GSet

namespace Convergent

/-- State: pair of GSets (added, removed) -/
structure TwoPSet (α : Type) [BEq α] [Hashable α] where
  added : GSet α
  removed : GSet α
  deriving Repr, Inhabited

/-- Operation: add or remove an element -/
inductive TwoPSetOp (α : Type) where
  | add (value : α)
  | remove (value : α)
  deriving BEq, Repr

namespace TwoPSet

variable {α : Type} [BEq α] [Hashable α]

/-- Empty set -/
def empty : TwoPSet α :=
  { added := GSet.empty, removed := GSet.empty }

/-- Check if an element is in the set -/
def contains (tps : TwoPSet α) (value : α) : Bool :=
  tps.added.contains value && !tps.removed.contains value

/-- Get all elements currently in the set -/
def toList (tps : TwoPSet α) : List α :=
  tps.added.toList.filter fun v => !tps.removed.contains v

/-- Apply an operation -/
def apply (tps : TwoPSet α) (op : TwoPSetOp α) : TwoPSet α :=
  match op with
  | .add value =>
    -- Only add if not already removed (tombstone check)
    if tps.removed.contains value then tps
    else { tps with added := tps.added.apply (GSet.add value) }
  | .remove value =>
    { tps with removed := tps.removed.apply (GSet.add value) }

/-- Create an add operation -/
def add (value : α) : TwoPSetOp α := .add value

/-- Create a remove operation -/
def remove (value : α) : TwoPSetOp α := .remove value

/-- Merge two TwoPSets -/
def merge (a b : TwoPSet α) : TwoPSet α :=
  { added := GSet.merge a.added b.added
  , removed := GSet.merge a.removed b.removed }

instance : CmRDT (TwoPSet α) (TwoPSetOp α) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (TwoPSet α) (TwoPSetOp α) (List α) where
  query := toList

instance [ToString α] : ToString (TwoPSet α) where
  toString tps :=
    let elems := tps.toList.map toString
    s!"TwoPSet(\{{", ".intercalate elems}})"

/-! ## Monadic Interface -/

/-- Add an element to the set in the CRDT monad -/
def addM (value : α) : CRDTM (TwoPSet α) Unit :=
  applyM (add value)

/-- Remove an element from the set in the CRDT monad -/
def removeM (value : α) : CRDTM (TwoPSet α) Unit :=
  applyM (remove value)

end TwoPSet

end Convergent
