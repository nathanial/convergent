/-
  CRDT Monad - StateM-based interface for cleaner operation chaining

  Provides a monadic interface for sequencing CRDT operations, replacing
  the verbose `|> fun s => Type.apply s op` pattern with `do` notation.

  ## Usage

  ```lean
  let gc := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r1
    GCounter.incM r1
  ```
-/
import Convergent.Core.CmRDT

namespace Convergent

/-- Monad for sequencing CRDT operations.
    This is just StateM specialized for CRDT state manipulation. -/
abbrev CRDTM (S : Type) := StateM S

/-- Run a CRDT computation starting from an initial state.
    Returns the final state after all operations are applied. -/
def runCRDT {S : Type} (initial : S) (m : CRDTM S Unit) : S :=
  (m.run initial).snd

/-- Run a CRDT computation starting from the empty state. -/
def runCRDT' {S : Type} {Op : Type} [inst : CmRDT S Op] (m : CRDTM S Unit) : S :=
  runCRDT inst.empty m

/-- Apply a single operation in the monad.
    This is the core building block for monadic CRDT operations. -/
def applyM {S : Type} {Op : Type} [inst : CmRDT S Op] (op : Op) : CRDTM S Unit := do
  let s ← get
  set (inst.apply s op)

/-- Apply multiple operations in sequence. -/
def applyManyM {S : Type} {Op : Type} [inst : CmRDT S Op] (ops : List Op) : CRDTM S Unit :=
  ops.forM applyM

/-- Get the current state. -/
def getState {S : Type} : CRDTM S S := get

/-- Query the current value using CmRDTQuery. -/
def queryM {S : Type} {Op : Type} {Q : Type} [inst : CmRDTQuery S Op Q] : CRDTM S Q := do
  let s ← get
  pure (inst.query s)

/-- Modify the state using a function. -/
def modifyState {S : Type} (f : S → S) : CRDTM S Unit :=
  modify f

/-- Merge another state into the current state. -/
def mergeM {S : Type} {Op : Type} [inst : CmRDT S Op] (other : S) : CRDTM S Unit := do
  let s ← get
  set (inst.merge s other)

end Convergent
