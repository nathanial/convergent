/-
  LWWRegister - Last-Writer-Wins Register

  A register that can hold a single value, with concurrent writes
  resolved by timestamp (last write wins).

  Operations:
  - Set: Write a new value with a timestamp

  The value with the highest timestamp wins. Ties are broken by replica ID.
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.Timestamp

namespace Convergent

/-- State: optional value with timestamp -/
structure LWWRegister (α : Type) where
  value : Option (α × LamportTs)
  deriving Repr, Inhabited

/-- Operation: set a value with timestamp -/
structure LWWRegisterOp (α : Type) where
  value : α
  timestamp : LamportTs
  deriving Repr

namespace LWWRegister

variable {α : Type}

/-- Empty register -/
def empty : LWWRegister α := { value := none }

/-- Get the current value (if any) -/
def get (reg : LWWRegister α) : Option α :=
  reg.value.map Prod.fst

/-- Get the current timestamp (if any) -/
def getTimestamp (reg : LWWRegister α) : Option LamportTs :=
  reg.value.map Prod.snd

/-- Apply a set operation.
    When timestamps are equal, uses value comparison as tie-breaker for commutativity. -/
def apply [Ord α] (reg : LWWRegister α) (op : LWWRegisterOp α) : LWWRegister α :=
  match reg.value with
  | none => { value := some (op.value, op.timestamp) }
  | some (existingVal, existingTs) =>
    match compare op.timestamp existingTs with
    | .gt => { value := some (op.value, op.timestamp) }
    | .lt => reg
    | .eq =>
      -- Equal timestamps: use value comparison as tie-breaker
      match compare op.value existingVal with
      | .gt => { value := some (op.value, op.timestamp) }
      | _ => reg

/-- Create a set operation -/
def set (value : α) (timestamp : LamportTs) : LWWRegisterOp α :=
  { value, timestamp }

/-- Merge two registers (take the one with higher timestamp).
    When timestamps are equal, uses value comparison as tie-breaker for commutativity. -/
def merge [Ord α] (a b : LWWRegister α) : LWWRegister α :=
  match a.value, b.value with
  | none, _ => b
  | _, none => a
  | some (valA, tsA), some (valB, tsB) =>
    match compare tsA tsB with
    | .gt => a
    | .lt => b
    | .eq =>
      -- Equal timestamps: use value as deterministic tie-breaker for commutativity
      match compare valA valB with
      | .gt => a
      | .lt => b
      | .eq => a  -- Values are equal, either choice works

instance [Ord α] : CmRDT (LWWRegister α) (LWWRegisterOp α) where
  empty := empty
  apply := apply
  merge := merge

instance [Ord α] : CmRDTQuery (LWWRegister α) (LWWRegisterOp α) (Option α) where
  query := get

instance [ToString α] : ToString (LWWRegister α) where
  toString reg := match reg.value with
    | none => "LWWRegister(empty)"
    | some (v, ts) => s!"LWWRegister({v} @ {ts})"

/-! ## Monadic Interface -/

/-- Set the register value with timestamp in the CRDT monad -/
def setM [Ord α] (value : α) (timestamp : LamportTs) : CRDTM (LWWRegister α) Unit :=
  applyM (set value timestamp)

end LWWRegister

end Convergent
