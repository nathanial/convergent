/-
  Timestamp - Logical clocks for ordering events in distributed systems

  Provides:
  - LamportTs: Lamport timestamps for total ordering
  - VectorClock: Vector clocks for causal ordering
-/
import Convergent.Core.ReplicaId
import Std.Data.HashMap

namespace Convergent

/-- Lamport timestamp for total ordering of events.
    When times are equal, replica ID breaks the tie. -/
structure LamportTs where
  time : Nat
  replica : ReplicaId
  deriving BEq, Repr, Inhabited, DecidableEq

namespace LamportTs

/-- Create a new Lamport timestamp -/
def new (time : Nat) (replica : ReplicaId) : LamportTs := { time, replica }

/-- Initial timestamp for a replica -/
def init (replica : ReplicaId) : LamportTs := { time := 0, replica }

/-- Increment the timestamp -/
def inc (ts : LamportTs) : LamportTs := { ts with time := ts.time + 1 }

/-- Update timestamp after receiving a message (take max + 1) -/
def update (local_ : LamportTs) (received : LamportTs) : LamportTs :=
  { local_ with time := max local_.time received.time + 1 }

/-- Total ordering: compare by time first, then by replica ID -/
instance : Ord LamportTs where
  compare a b :=
    match compare a.time b.time with
    | .eq => compare a.replica b.replica
    | other => other

instance : LT LamportTs where
  lt a b := match Ord.compare a b with
    | .lt => True
    | _ => False

instance : LE LamportTs where
  le a b := match Ord.compare a b with
    | .gt => False
    | _ => True

instance (a b : LamportTs) : Decidable (a < b) :=
  match h : Ord.compare a b with
  | .lt => isTrue (by simp only [LT.lt]; rw [h]; trivial)
  | .eq => isFalse (by simp only [LT.lt]; rw [h]; intro h; cases h)
  | .gt => isFalse (by simp only [LT.lt]; rw [h]; intro h; cases h)

instance (a b : LamportTs) : Decidable (a <= b) :=
  match h : Ord.compare a b with
  | .lt => isTrue (by simp only [LE.le]; rw [h]; trivial)
  | .eq => isTrue (by simp only [LE.le]; rw [h]; trivial)
  | .gt => isFalse (by simp only [LE.le]; rw [h]; intro h; cases h)

instance : ToString LamportTs where
  toString ts := s!"({ts.time}, {ts.replica})"

end LamportTs

/-- Vector clock for tracking causal relationships.
    Maps each replica to its logical time. -/
structure VectorClock where
  clocks : Std.HashMap ReplicaId Nat
  deriving Repr, Inhabited

namespace VectorClock

/-- Empty vector clock -/
def empty : VectorClock := { clocks := {} }

/-- Get the time for a specific replica -/
def get (vc : VectorClock) (replica : ReplicaId) : Nat :=
  vc.clocks.getD replica 0

/-- Increment the clock for a specific replica -/
def inc (vc : VectorClock) (replica : ReplicaId) : VectorClock :=
  { clocks := vc.clocks.insert replica (vc.get replica + 1) }

/-- Merge two vector clocks (take component-wise max) -/
def merge (a b : VectorClock) : VectorClock :=
  let merged := a.clocks.fold (init := b.clocks) fun acc replica time =>
    acc.insert replica (max time (b.get replica))
  { clocks := merged }

/-- Check if `a` happened before `b` (a < b).
    a < b iff all(a[i] <= b[i]) and exists(a[j] < b[j]) -/
def happenedBefore (a b : VectorClock) : Bool :=
  let aList := a.clocks.toList
  let bList := b.clocks.toList
  let allLe := aList.all fun (replica, time) => time <= b.get replica
  let someLt := aList.any fun (replica, time) => time < b.get replica
  let bHasMore := bList.any fun (replica, time) => time > a.get replica
  allLe && (someLt || bHasMore)

/-- Check if two vector clocks are concurrent (neither happened before the other) -/
def concurrent (a b : VectorClock) : Bool :=
  !happenedBefore a b && !happenedBefore b a

/-- Check if `a` dominates `b` (a >= b component-wise) -/
def dominates (a b : VectorClock) : Bool :=
  b.clocks.toList.all fun (replica, time) => a.get replica >= time

instance : BEq VectorClock where
  beq a b :=
    let aKeys := a.clocks.toList.map Prod.fst
    let bKeys := b.clocks.toList.map Prod.fst
    let allKeys := aKeys ++ bKeys
    allKeys.all fun r => a.get r == b.get r

instance : ToString VectorClock where
  toString vc :=
    let pairs := vc.clocks.toList.map fun (r, t) => s!"{r}:{t}"
    s!"[{", ".intercalate pairs}]"

end VectorClock

end Convergent
