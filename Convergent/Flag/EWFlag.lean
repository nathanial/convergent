/-
  EWFlag - Enable-Wins Flag

  A boolean flag CRDT where concurrent enable and disable operations
  result in the flag being enabled (enable-wins semantics).

  State: Two GSets tracking which replicas have enabled/disabled.
  Query: True if any replica has enabled (regardless of disables).

  Operations:
  - Enable: Add replica to enabled set
  - Disable: Add replica to disabled set (tracked for commutativity)
-/
import Convergent.Core.CmRDT
import Convergent.Core.ReplicaId
import Convergent.Set.GSet

namespace Convergent

/-- State: tracks which replicas have enabled/disabled the flag -/
structure EWFlag where
  enabled : GSet ReplicaId
  disabled : GSet ReplicaId
  deriving Repr, Inhabited

/-- Operation: enable or disable the flag -/
inductive EWFlagOp where
  | enable (replica : ReplicaId)
  | disable (replica : ReplicaId)
  deriving Repr, BEq

namespace EWFlag

/-- Empty flag (disabled by default) -/
def empty : EWFlag := { enabled := GSet.empty, disabled := GSet.empty }

/-- Get the flag value. Enable-wins: true if any replica has enabled. -/
def value (f : EWFlag) : Bool := !f.enabled.elements.isEmpty

/-- Apply an operation -/
def apply (f : EWFlag) (op : EWFlagOp) : EWFlag :=
  match op with
  | .enable r => { f with enabled := GSet.apply f.enabled (GSet.add r) }
  | .disable r => { f with disabled := GSet.apply f.disabled (GSet.add r) }

/-- Create an enable operation -/
def enable (replica : ReplicaId) : EWFlagOp := .enable replica

/-- Create a disable operation -/
def disable (replica : ReplicaId) : EWFlagOp := .disable replica

/-- Merge two flags (union both sets) -/
def merge (a b : EWFlag) : EWFlag :=
  { enabled := GSet.merge a.enabled b.enabled
  , disabled := GSet.merge a.disabled b.disabled }

instance : CmRDT EWFlag EWFlagOp where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery EWFlag EWFlagOp Bool where
  query := value

instance : ToString EWFlag where
  toString f := s!"EWFlag({f.value})"

end EWFlag

end Convergent
