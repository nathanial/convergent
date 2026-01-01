/-
  GCounter - Grow-only Counter

  A counter that can only be incremented, never decremented.
  Each replica maintains its own count, and the total value
  is the sum of all replica counts.

  Operations:
  - Increment: Add 1 to the specified replica's count

  This is the simplest CRDT - increment operations trivially commute.
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.ReplicaId
import Std.Data.HashMap

namespace Convergent

/-- State: per-replica counts -/
structure GCounter where
  counts : Std.HashMap ReplicaId Nat
  deriving Repr, Inhabited

/-- Operation: increment a specific replica's count by a given amount -/
structure GCounterOp where
  replica : ReplicaId
  amount : Nat := 1
  deriving BEq, Repr, Inhabited

namespace GCounter

/-- Empty counter -/
def empty : GCounter := { counts := {} }

/-- Get the count for a specific replica -/
def getCount (gc : GCounter) (replica : ReplicaId) : Nat :=
  gc.counts.getD replica 0

/-- Get the total counter value (sum of all replica counts) -/
def value (gc : GCounter) : Nat :=
  gc.counts.fold (init := 0) fun acc _ count => acc + count

/-- Apply an increment operation -/
def apply (gc : GCounter) (op : GCounterOp) : GCounter :=
  { counts := gc.counts.insert op.replica (gc.getCount op.replica + op.amount) }

/-- Create an increment operation for a replica (increment by 1) -/
def increment (replica : ReplicaId) : GCounterOp :=
  { replica, amount := 1 }

/-- Create an increment-by-N operation for a replica -/
def incrementBy (replica : ReplicaId) (n : Nat) : GCounterOp :=
  { replica, amount := n }

/-- Merge two GCounters (state-based merge for recovery/sync) -/
def merge (a b : GCounter) : GCounter :=
  let merged := a.counts.fold (init := b.counts) fun acc replica count =>
    acc.insert replica (max count (b.getCount replica))
  { counts := merged }

instance : CmRDT GCounter GCounterOp where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery GCounter GCounterOp Nat where
  query := value

instance : ToString GCounter where
  toString gc := s!"GCounter({gc.value})"

/-! ## Monadic Interface -/

/-- Increment the counter by 1 in the CRDT monad -/
def incM (replica : ReplicaId) : CRDTM GCounter Unit :=
  applyM (increment replica)

/-- Increment the counter by N in the CRDT monad -/
def incByM (replica : ReplicaId) (n : Nat) : CRDTM GCounter Unit :=
  applyM (incrementBy replica n)

end GCounter

end Convergent
