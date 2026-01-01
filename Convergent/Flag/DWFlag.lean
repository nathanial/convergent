/-
  DWFlag - Disable-Wins Flag

  A boolean flag CRDT where concurrent enable and disable operations
  result in the flag being disabled (disable-wins semantics).

  State: Two GSets tracking which replicas have enabled/disabled.
  Query: True only if some replica has enabled AND no replica has disabled.

  Operations:
  - Enable: Add replica to enabled set
  - Disable: Add replica to disabled set
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.ReplicaId
import Convergent.Set.GSet

namespace Convergent

/-- State: tracks which replicas have enabled/disabled the flag -/
structure DWFlag where
  enabled : GSet ReplicaId
  disabled : GSet ReplicaId
  deriving Repr, Inhabited

/-- Operation: enable or disable the flag -/
inductive DWFlagOp where
  | enable (replica : ReplicaId)
  | disable (replica : ReplicaId)
  deriving Repr, BEq

namespace DWFlag

/-- Empty flag (disabled by default) -/
def empty : DWFlag := { enabled := GSet.empty, disabled := GSet.empty }

/-- Get the flag value. Disable-wins: true only if enabled AND no disables. -/
def value (f : DWFlag) : Bool := !f.enabled.elements.isEmpty && f.disabled.elements.isEmpty

/-- Apply an operation -/
def apply (f : DWFlag) (op : DWFlagOp) : DWFlag :=
  match op with
  | .enable r => { f with enabled := GSet.apply f.enabled (GSet.add r) }
  | .disable r => { f with disabled := GSet.apply f.disabled (GSet.add r) }

/-- Create an enable operation -/
def enable (replica : ReplicaId) : DWFlagOp := .enable replica

/-- Create a disable operation -/
def disable (replica : ReplicaId) : DWFlagOp := .disable replica

/-- Merge two flags (union both sets) -/
def merge (a b : DWFlag) : DWFlag :=
  { enabled := GSet.merge a.enabled b.enabled
  , disabled := GSet.merge a.disabled b.disabled }

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
def enableM (replica : ReplicaId) : CRDTM DWFlag Unit :=
  applyM (enable replica)

/-- Disable the flag in the CRDT monad -/
def disableM (replica : ReplicaId) : CRDTM DWFlag Unit :=
  applyM (disable replica)

end DWFlag

end Convergent
