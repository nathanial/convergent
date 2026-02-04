/-
  DWFlag - Disable-Wins Flag

  A boolean flag CRDT where concurrent enable and disable operations
  result in the flag being disabled (disable-wins semantics).

  State: timestamps for the most recent enable and disable operations.
  Query: true if the last enable is newer than the last disable.
  If timestamps are equal (concurrent), disable wins.

  Operations:
  - Enable: Record enable timestamp
  - Disable: Record disable timestamp
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.Timestamp

namespace Convergent

/-- State: tracks which replicas have enabled/disabled the flag -/
structure DWFlag where
  lastEnable : Option LamportTs
  lastDisable : Option LamportTs
  deriving Repr, Inhabited

/-- Operation: enable or disable the flag -/
inductive DWFlagOp where
  | enable (timestamp : LamportTs)
  | disable (timestamp : LamportTs)
  deriving Repr, BEq

namespace DWFlag

/-- Empty flag (disabled by default) -/
def empty : DWFlag := { lastEnable := none, lastDisable := none }

/-- Max by Lamport timestamp (time, then replica) for deterministic merge. -/
private def maxTs (a b : LamportTs) : LamportTs :=
  match compare a b with
  | .gt => a
  | .lt => b
  | .eq => a

/-- Max option helper for timestamps. -/
private def maxTsOpt (a b : Option LamportTs) : Option LamportTs :=
  match a, b with
  | none, none => none
  | some ts, none => some ts
  | none, some ts => some ts
  | some tsA, some tsB => some (maxTs tsA tsB)

/-- Update an optional timestamp with a new one. -/
private def updateTs (current : Option LamportTs) (ts : LamportTs) : Option LamportTs :=
  maxTsOpt current (some ts)

/-- Get the flag value. Disable-wins on equal timestamps. -/
def value (f : DWFlag) : Bool :=
  match f.lastEnable, f.lastDisable with
  | none, none => false
  | some _, none => true
  | none, some _ => false
  | some en, some dis =>
    match compare en.time dis.time with
    | .gt => true
    | .lt => false
    | .eq => false

/-- Apply an operation -/
def apply (f : DWFlag) (op : DWFlagOp) : DWFlag :=
  match op with
  | .enable ts => { f with lastEnable := updateTs f.lastEnable ts }
  | .disable ts => { f with lastDisable := updateTs f.lastDisable ts }

/-- Create an enable operation -/
def enable (timestamp : LamportTs) : DWFlagOp := .enable timestamp

/-- Create a disable operation -/
def disable (timestamp : LamportTs) : DWFlagOp := .disable timestamp

/-- Merge two flags (union both sets) -/
def merge (a b : DWFlag) : DWFlag :=
  { lastEnable := maxTsOpt a.lastEnable b.lastEnable
  , lastDisable := maxTsOpt a.lastDisable b.lastDisable }

instance : CmRDT DWFlag DWFlagOp where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery DWFlag DWFlagOp Bool where
  query := value

instance : ToString DWFlag where
  toString f := s!"DWFlag({f.value})"

/-! ## Monadic Interface -/

/-- Enable the flag in the CRDT monad -/
def enableM (timestamp : LamportTs) : CRDTM DWFlag Unit :=
  applyM (enable timestamp)

/-- Disable the flag in the CRDT monad -/
def disableM (timestamp : LamportTs) : CRDTM DWFlag Unit :=
  applyM (disable timestamp)

end DWFlag

end Convergent
