/-
  MVRegister - Multi-Value Register

  A register that preserves all concurrent writes. When concurrent
  writes occur, all values are kept until a subsequent write that
  causally depends on all of them.

  Operations:
  - Set: Write a new value with a vector clock

  Query returns a list of all concurrent values.
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.Timestamp

namespace Convergent

/-- State: list of (value, vector clock) pairs representing concurrent values -/
structure MVRegister (α : Type) where
  values : List (α × VectorClock)
  deriving Repr, Inhabited

/-- Operation: set a value with vector clock -/
structure MVRegisterOp (α : Type) where
  value : α
  clock : VectorClock
  deriving Repr

namespace MVRegister

variable {α : Type}

/-- Empty register -/
def empty : MVRegister α := { values := [] }

/-- Get all current values (concurrent writes) -/
def get (reg : MVRegister α) : List α :=
  reg.values.map Prod.fst

/-- Get all values with their vector clocks -/
def getWithClocks (reg : MVRegister α) : List (α × VectorClock) :=
  reg.values

/-- Check if a value with its clock is dominated by any existing value -/
private def isDominated (clock : VectorClock) (values : List (α × VectorClock)) : Bool :=
  values.any fun (_, existingClock) => VectorClock.dominates existingClock clock

/-- Check if two clocks are equivalent (mutually dominate) -/
private def clocksEqual (a b : VectorClock) : Bool :=
  VectorClock.dominates a b && VectorClock.dominates b a

/-- Check if dominated by a strictly greater clock (not equivalent) -/
private def isStrictlyDominated (clock : VectorClock) (values : List (α × VectorClock)) : Bool :=
  values.any fun (_, existingClock) =>
    VectorClock.dominates existingClock clock && !clocksEqual existingClock clock

/-- Remove values that are strictly dominated by the new clock -/
private def removeDominated (clock : VectorClock) (values : List (α × VectorClock)) : List (α × VectorClock) :=
  values.filter fun (_, existingClock) =>
    !VectorClock.dominates clock existingClock || clocksEqual clock existingClock

/-- Apply a set operation.
    - If the new value's clock is strictly dominated, ignore it
    - If clocks are equivalent, use value comparison as tie-breaker
    - Otherwise, add it as a concurrent value -/
def apply [Ord α] (reg : MVRegister α) (op : MVRegisterOp α) : MVRegister α :=
  -- Check if strictly dominated (not equivalent)
  if isStrictlyDominated op.clock reg.values then
    reg
  else
    let remaining := reg.values.filter fun (existingVal, existingClock) =>
      if clocksEqual existingClock op.clock then
        compare existingVal op.value == .gt
      else
        !VectorClock.dominates op.clock existingClock
    -- Only add new value if no equivalent clock with greater value exists
    let hasGreaterEquivalent := reg.values.any fun (existingVal, existingClock) =>
      clocksEqual existingClock op.clock && compare existingVal op.value == .gt
    if hasGreaterEquivalent then
      { values := remaining }
    else
      { values := (op.value, op.clock) :: remaining }

/-- Create a set operation -/
def set (value : α) (clock : VectorClock) : MVRegisterOp α :=
  { value, clock }

/-- Check if two vector clocks are equivalent (mutually dominate) -/
private def clocksEquivalent (a b : VectorClock) : Bool :=
  VectorClock.dominates a b && VectorClock.dominates b a

/-- Canonical clock entries (sorted by replica id, drop zero times). -/
private def clockEntries (vc : VectorClock) : List (ReplicaId × Nat) :=
  let filtered := vc.clocks.toList.filter fun (_, t) => t != 0
  let sorted := filtered.toArray.qsort fun (r1, _) (r2, _) => r1 < r2
  sorted.toList

/-- Compare clock entry lists lexicographically. -/
private def compareEntries : List (ReplicaId × Nat) → List (ReplicaId × Nat) → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | (r1, t1) :: xs, (r2, t2) :: ys =>
    match compare r1 r2 with
    | .eq =>
      match compare t1 t2 with
      | .eq => compareEntries xs ys
      | other => other
    | other => other

/-- Compare vector clocks for deterministic ordering. -/
private def compareClock (a b : VectorClock) : Ordering :=
  compareEntries (clockEntries a) (clockEntries b)

/-- Merge two registers (keep all non-dominated values from both).
    Uses deterministic ordering to ensure commutativity. -/
def merge [BEq α] [Ord α] (a b : MVRegister α) : MVRegister α :=
  let combined := a.values ++ b.values
  -- Sort by (clock, value) to ensure deterministic processing order
  let sorted := combined.toArray.qsort fun (v1, vc1) (v2, vc2) =>
    match compareClock vc1 vc2 with
    | .lt => true
    | .gt => false
    | .eq => compare v1 v2 == .gt
  -- Remove dominated values, keeping only non-dominated ones
  let filtered := sorted.toList.foldl (init := []) fun acc (v, vc) =>
    if isDominated vc acc then acc
    else (v, vc) :: removeDominated vc acc
  -- Sort result for consistent output order
  let result := filtered.toArray.qsort fun (v1, vc1) (v2, vc2) =>
    match compareClock vc1 vc2 with
    | .lt => true
    | .gt => false
    | .eq => compare v1 v2 == .gt
  { values := result.toList }

instance [BEq α] [Ord α] : CmRDT (MVRegister α) (MVRegisterOp α) where
  empty := empty
  apply := apply
  merge := merge

instance [BEq α] [Ord α] : CmRDTQuery (MVRegister α) (MVRegisterOp α) (List α) where
  query := get

instance [ToString α] : ToString (MVRegister α) where
  toString reg :=
    let vals := reg.values.map fun (v, _) => toString v
    s!"MVRegister([{", ".intercalate vals}])"

/-! ## Monadic Interface -/

/-- Set the register value with vector clock in the CRDT monad -/
def setM [BEq α] [Ord α] (value : α) (clock : VectorClock) : CRDTM (MVRegister α) Unit :=
  applyM (set value clock)

end MVRegister

end Convergent
