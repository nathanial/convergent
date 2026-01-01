/-
  PNCounter - Positive-Negative Counter

  A counter that supports both increment and decrement operations.
  Implemented as two GCounters: one for positive increments, one for negative.
  The value is positive.value - negative.value.

  Operations:
  - Increment: Add 1 to the positive counter
  - Decrement: Add 1 to the negative counter
-/
import Convergent.Core.CmRDT
import Convergent.Core.ReplicaId
import Convergent.Counter.GCounter

namespace Convergent

/-- State: pair of GCounters (positive, negative) -/
structure PNCounter where
  positive : GCounter
  negative : GCounter
  deriving Repr, Inhabited

/-- Operation: increment or decrement by a given amount -/
inductive PNCounterOp where
  | increment (replica : ReplicaId) (amount : Nat := 1)
  | decrement (replica : ReplicaId) (amount : Nat := 1)
  deriving BEq, Repr, Inhabited

namespace PNCounter

/-- Empty counter -/
def empty : PNCounter :=
  { positive := GCounter.empty, negative := GCounter.empty }

/-- Get the counter value (positive - negative) -/
def value (pn : PNCounter) : Int :=
  Int.ofNat pn.positive.value - Int.ofNat pn.negative.value

/-- Apply an operation -/
def apply (pn : PNCounter) (op : PNCounterOp) : PNCounter :=
  match op with
  | .increment replica amount =>
    { pn with positive := pn.positive.apply (GCounter.incrementBy replica amount) }
  | .decrement replica amount =>
    { pn with negative := pn.negative.apply (GCounter.incrementBy replica amount) }

/-- Create an increment operation (by 1) -/
def increment (replica : ReplicaId) : PNCounterOp :=
  .increment replica 1

/-- Create an increment-by-N operation -/
def incrementBy (replica : ReplicaId) (n : Nat) : PNCounterOp :=
  .increment replica n

/-- Create a decrement operation (by 1) -/
def decrement (replica : ReplicaId) : PNCounterOp :=
  .decrement replica 1

/-- Create a decrement-by-N operation -/
def decrementBy (replica : ReplicaId) (n : Nat) : PNCounterOp :=
  .decrement replica n

/-- Merge two PNCounters -/
def merge (a b : PNCounter) : PNCounter :=
  { positive := GCounter.merge a.positive b.positive
  , negative := GCounter.merge a.negative b.negative }

instance : CmRDT PNCounter PNCounterOp where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery PNCounter PNCounterOp Int where
  query := value

instance : ToString PNCounter where
  toString pn := s!"PNCounter({pn.value})"

/-! ## Monadic Interface -/

/-- Increment the counter by 1 in the CRDT monad -/
def incM (replica : ReplicaId) : CRDTM PNCounter Unit :=
  applyM (increment replica)

/-- Increment the counter by N in the CRDT monad -/
def incByM (replica : ReplicaId) (n : Nat) : CRDTM PNCounter Unit :=
  applyM (incrementBy replica n)

/-- Decrement the counter by 1 in the CRDT monad -/
def decM (replica : ReplicaId) : CRDTM PNCounter Unit :=
  applyM (decrement replica)

/-- Decrement the counter by N in the CRDT monad -/
def decByM (replica : ReplicaId) (n : Nat) : CRDTM PNCounter Unit :=
  applyM (decrementBy replica n)

end PNCounter

end Convergent
