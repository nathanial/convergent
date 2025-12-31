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

/-- Remove values that are dominated by the new clock -/
private def removeDominated (clock : VectorClock) (values : List (α × VectorClock)) : List (α × VectorClock) :=
  values.filter fun (_, existingClock) => !VectorClock.dominates clock existingClock

/-- Apply a set operation.
    - If the new value's clock dominates existing values, remove them
    - If the new value is dominated, ignore it
    - Otherwise, add it as a concurrent value -/
def apply (reg : MVRegister α) (op : MVRegisterOp α) : MVRegister α :=
  if isDominated op.clock reg.values then
    -- New value is dominated, ignore it
    reg
  else
    -- Remove dominated values and add new value
    let remaining := removeDominated op.clock reg.values
    { values := (op.value, op.clock) :: remaining }

/-- Create a set operation -/
def set (value : α) (clock : VectorClock) : MVRegisterOp α :=
  { value, clock }

/-- Check if two vector clocks are equivalent (mutually dominate) -/
private def clocksEquivalent (a b : VectorClock) : Bool :=
  VectorClock.dominates a b && VectorClock.dominates b a

/-- Compare vector clocks for deterministic ordering -/
private def compareClock (a b : VectorClock) : Ordering :=
  -- Use string representation for deterministic comparison
  compare (toString a) (toString b)

/-- Merge two registers (keep all non-dominated values from both).
    Uses deterministic ordering to ensure commutativity. -/
def merge [BEq α] [Ord α] (a b : MVRegister α) : MVRegister α :=
  let combined := a.values ++ b.values
  -- Sort by (clock, value) to ensure deterministic processing order
  let sorted := combined.toArray.qsort fun (v1, vc1) (v2, vc2) =>
    match compareClock vc1 vc2 with
    | .lt => true
    | .gt => false
    | .eq => compare v1 v2 == .lt
  -- Remove dominated values, keeping only non-dominated ones
  let filtered := sorted.toList.foldl (init := []) fun acc (v, vc) =>
    if isDominated vc acc then acc
    else (v, vc) :: removeDominated vc acc
  -- Sort result for consistent output order
  let result := filtered.toArray.qsort fun (v1, vc1) (v2, vc2) =>
    match compareClock vc1 vc2 with
    | .lt => true
    | .gt => false
    | .eq => compare v1 v2 == .lt
  { values := result.toList }

instance : CmRDT (MVRegister α) (MVRegisterOp α) where
  empty := empty
  apply := apply

instance : CmRDTQuery (MVRegister α) (MVRegisterOp α) (List α) where
  query := get

instance [ToString α] : ToString (MVRegister α) where
  toString reg :=
    let vals := reg.values.map fun (v, _) => toString v
    s!"MVRegister([{", ".intercalate vals}])"

end MVRegister

end Convergent
