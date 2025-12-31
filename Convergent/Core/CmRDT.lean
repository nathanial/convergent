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

end Convergent
