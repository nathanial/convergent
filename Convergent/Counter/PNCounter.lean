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

/-- Operation: increment or decrement -/
inductive PNCounterOp where
  | increment (replica : ReplicaId)
  | decrement (replica : ReplicaId)
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
  | .increment replica =>
    { pn with positive := pn.positive.apply (GCounter.increment replica) }
  | .decrement replica =>
    { pn with negative := pn.negative.apply (GCounter.increment replica) }

/-- Create an increment operation -/
def increment (replica : ReplicaId) : PNCounterOp :=
  .increment replica

/-- Create a decrement operation -/
def decrement (replica : ReplicaId) : PNCounterOp :=
  .decrement replica

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

end PNCounter

end Convergent
