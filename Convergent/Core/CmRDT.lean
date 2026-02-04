/-
  CmRDT - Operation-based Conflict-free Replicated Data Types

  This module defines the core typeclass for operation-based CRDTs.
  In CmRDTs, replicas exchange operations rather than full state.

  Key requirements for correctness:
  - Operations must be delivered to all replicas (reliable broadcast)
  - Concurrent operations must commute when applied in any order
  - Operations are applied exactly once (deduplication may be needed)
-/
namespace Convergent

/-- Core typeclass for operation-based CRDTs (CmRDTs).

    Type parameters:
    - `S`: The state type
    - `Op`: The operation type

    The `apply` function must satisfy commutativity for concurrent operations:
    `apply (apply s op1) op2 = apply (apply s op2) op1`
    when op1 and op2 are concurrent (neither causally depends on the other).
-/
class CmRDT (S : Type u) (Op : Type v) where
  /-- Initial empty state -/
  empty : S
  /-- Apply an operation to state, producing new state -/
  apply : S → Op → S
  /-- Merge two states (for state-based synchronization and nested CRDTs) -/
  merge : S → S → S

namespace CmRDT

/-- Apply a list of operations sequentially -/
def applyMany {S : Type u} {Op : Type v} [inst : CmRDT S Op] (state : S) (ops : List Op) : S :=
  ops.foldl inst.apply state

/-- Create initial state and apply a list of operations -/
def fromOps {S : Type u} {Op : Type v} [inst : CmRDT S Op] (ops : List Op) : S :=
  applyMany inst.empty ops

end CmRDT

/-- Extended typeclass for CmRDTs that support querying -/
class CmRDTQuery (S : Type u) (Op : Type v) (Q : Type w) extends CmRDT S Op where
  /-- Query the current value from state -/
  query : S → Q

/-! ## Trivial CmRDT instances for simple immutable types

These allow using simple types as values in nested CRDT structures like ORMap.
Operations are no-ops. Merge picks the maximum value by the type's ordering to
ensure commutativity and deterministic convergence if replicas diverge.
-/

instance : CmRDT Nat Unit where
  empty := 0
  apply n _ := n
  merge a b := if a <= b then b else a

instance : CmRDT Int Unit where
  empty := 0
  apply n _ := n
  merge a b := if a <= b then b else a

instance : CmRDT String Unit where
  empty := ""
  apply s _ := s
  merge a b := match compare a b with
    | .lt => b
    | _ => a

instance : CmRDT Bool Unit where
  empty := false
  apply b _ := b
  merge a b := a || b

end Convergent
