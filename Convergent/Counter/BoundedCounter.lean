/-
  BoundedCounter - Counter with Min/Max Bounds

  A counter that supports increment and decrement with soft bounds.
  The internal PNCounter tracks all operations for proper CRDT semantics,
  while the query result is clamped to the configured bounds.

  Soft bounds design:
  - Operations always apply internally (preserves commutativity)
  - Query value is clamped to [min, max]
  - Merge works correctly (PNCounter merge semantics)

  This ensures proper CmRDT properties while providing bounded visible values.

  Use cases: rate limiting, inventory, quotas, bounded resources.

  Note: All replicas should use the same min/max bounds.
-/
import Convergent.Core.CmRDT
import Convergent.Core.ReplicaId
import Convergent.Counter.PNCounter

namespace Convergent

/-- State: PNCounter with min/max bounds -/
structure BoundedCounter where
  counter : PNCounter
  min : Int
  max : Int
  deriving Repr, Inhabited

/-- Operation: increment or decrement -/
inductive BoundedCounterOp where
  | increment (replica : ReplicaId)
  | decrement (replica : ReplicaId)
  deriving BEq, Repr, Inhabited

namespace BoundedCounter

/-- Create an empty bounded counter with specified bounds -/
def empty (min max : Int := 0) : BoundedCounter :=
  { counter := PNCounter.empty, min := min, max := max }

/-- Create a bounded counter with default bounds [0, 100] -/
def default : BoundedCounter := empty 0 100

/-- Get the raw (unclamped) counter value -/
def rawValue (bc : BoundedCounter) : Int :=
  bc.counter.value

/-- Get the counter value (clamped to bounds) -/
def value (bc : BoundedCounter) : Int :=
  let raw := bc.counter.value
  if raw < bc.min then bc.min
  else if raw > bc.max then bc.max
  else raw

/-- Check if counter is at maximum -/
def atMax (bc : BoundedCounter) : Bool :=
  bc.value >= bc.max

/-- Check if counter is at minimum -/
def atMin (bc : BoundedCounter) : Bool :=
  bc.value <= bc.min

/-- Apply an operation. Operations always apply internally for CRDT commutativity.
    The visible value is clamped via the `value` query. -/
def apply (bc : BoundedCounter) (op : BoundedCounterOp) : BoundedCounter :=
  match op with
  | .increment replica =>
    { bc with counter := PNCounter.apply bc.counter (.increment replica) }
  | .decrement replica =>
    { bc with counter := PNCounter.apply bc.counter (.decrement replica) }

/-- Create an increment operation -/
def increment (replica : ReplicaId) : BoundedCounterOp :=
  .increment replica

/-- Create a decrement operation -/
def decrement (replica : ReplicaId) : BoundedCounterOp :=
  .decrement replica

/-- Merge two BoundedCounters. Assumes same bounds. -/
def merge (a b : BoundedCounter) : BoundedCounter :=
  { counter := PNCounter.merge a.counter b.counter
  , min := a.min
  , max := a.max }

/-- CmRDT instance using default bounds -/
instance : CmRDT BoundedCounter BoundedCounterOp where
  empty := default
  apply := apply
  merge := merge

instance : CmRDTQuery BoundedCounter BoundedCounterOp Int where
  query := value

instance : ToString BoundedCounter where
  toString bc := s!"BoundedCounter({bc.value}, min={bc.min}, max={bc.max})"

end BoundedCounter

end Convergent
