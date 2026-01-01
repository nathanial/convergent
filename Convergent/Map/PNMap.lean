/-
  PNMap - Positive-Negative Counter Map

  A map where each key maps to a PNCounter value. Supports per-key
  increment and decrement operations. Counters are created automatically
  on first access (starting at 0).

  State: Maps each key to a PNCounter.

  Operations:
  - Increment: Add 1 to the counter at a key
  - Decrement: Subtract 1 from the counter at a key
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.ReplicaId
import Convergent.Counter.PNCounter
import Std.Data.HashMap

namespace Convergent

/-- State: key → PNCounter -/
structure PNMap (κ : Type) [BEq κ] [Hashable κ] where
  entries : Std.HashMap κ PNCounter
  deriving Repr, Inhabited

/-- Operation: increment or decrement at a key -/
inductive PNMapOp (κ : Type) where
  | increment (key : κ) (replica : ReplicaId)
  | decrement (key : κ) (replica : ReplicaId)
  deriving Repr

namespace PNMap

variable {κ : Type} [BEq κ] [Hashable κ]

/-- Empty map -/
def empty : PNMap κ := { entries := {} }

/-- Get the counter value for a key (0 if not present) -/
def get (m : PNMap κ) (key : κ) : Int :=
  (m.entries.getD key PNCounter.empty).value

/-- Get the PNCounter at a key (empty counter if not present) -/
def getCounter (m : PNMap κ) (key : κ) : PNCounter :=
  m.entries.getD key PNCounter.empty

/-- Check if a key has been modified (has a counter) -/
def contains (m : PNMap κ) (key : κ) : Bool :=
  m.entries.contains key

/-- Get all keys that have counters -/
def keys (m : PNMap κ) : List κ :=
  m.entries.toList.map Prod.fst

/-- Get all key-value pairs -/
def toList (m : PNMap κ) : List (κ × Int) :=
  m.entries.toList.map fun (k, c) => (k, c.value)

/-- Get the number of keys -/
def size (m : PNMap κ) : Nat :=
  m.entries.size

/-- Apply an operation -/
def apply (m : PNMap κ) (op : PNMapOp κ) : PNMap κ :=
  match op with
  | .increment key replica =>
    let counter := m.entries.getD key PNCounter.empty
    let counter' := PNCounter.apply counter (PNCounter.increment replica)
    { entries := m.entries.insert key counter' }
  | .decrement key replica =>
    let counter := m.entries.getD key PNCounter.empty
    let counter' := PNCounter.apply counter (PNCounter.decrement replica)
    { entries := m.entries.insert key counter' }

/-- Create an increment operation -/
def increment (key : κ) (replica : ReplicaId) : PNMapOp κ :=
  .increment key replica

/-- Create a decrement operation -/
def decrement (key : κ) (replica : ReplicaId) : PNMapOp κ :=
  .decrement key replica

/-- Merge two PNMaps (merge PNCounters for each key) -/
def merge (a b : PNMap κ) : PNMap κ :=
  let merged := a.entries.fold (init := b.entries) fun acc key counterA =>
    match acc[key]? with
    | none => acc.insert key counterA
    | some counterB => acc.insert key (PNCounter.merge counterA counterB)
  { entries := merged }

instance : CmRDT (PNMap κ) (PNMapOp κ) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (PNMap κ) (PNMapOp κ) (List (κ × Int)) where
  query := toList

instance [ToString κ] : ToString (PNMap κ) where
  toString m :=
    let pairs := m.toList.map fun (k, v) => s!"{k}: {v}"
    s!"PNMap(\{{", ".intercalate pairs}})"

/-! ## Monadic Interface -/

/-- Increment the counter at a key in the CRDT monad -/
def incM (key : κ) (replica : ReplicaId) : CRDTM (PNMap κ) Unit :=
  applyM (increment key replica)

/-- Decrement the counter at a key in the CRDT monad -/
def decM (key : κ) (replica : ReplicaId) : CRDTM (PNMap κ) Unit :=
  applyM (decrement key replica)

end PNMap

end Convergent
