/-
  LWWMap - Last-Writer-Wins Map

  A key-value map where concurrent writes to the same key are
  resolved by timestamp (last write wins). Supports put and delete.

  State: Maps each key to (Option value, timestamp).
  - Some value: key is present with that value
  - None: key has been deleted

  The timestamp determines which operation wins for concurrent updates.

  Operations:
  - Put: Set a key to a value
  - Delete: Remove a key
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.Timestamp
import Std.Data.HashMap

namespace Convergent

/-- State: key → (optional value, timestamp) -/
structure LWWMap (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  entries : Std.HashMap κ (Option α × LamportTs)
  deriving Repr, Inhabited

/-- Operation: put a value or delete -/
inductive LWWMapOp (κ : Type) (α : Type) where
  | put (key : κ) (value : α) (timestamp : LamportTs)
  | delete (key : κ) (timestamp : LamportTs)
  deriving Repr

namespace LWWMap

variable {κ : Type} {α : Type} [BEq κ] [Hashable κ]

/-- Empty map -/
def empty : LWWMap κ α := { entries := {} }

/-- Get a value by key (returns None if not present or deleted) -/
def get (m : LWWMap κ α) (key : κ) : Option α :=
  match m.entries[key]? with
  | some (value, _) => value
  | none => none

/-- Check if a key is present (and not deleted) -/
def contains (m : LWWMap κ α) (key : κ) : Bool :=
  match m.entries[key]? with
  | some (some _, _) => true
  | _ => false

/-- Get all keys that are present (not deleted) -/
def keys (m : LWWMap κ α) : List κ :=
  m.entries.toList.filterMap fun (k, (v, _)) =>
    if v.isSome then some k else none

/-- Get all key-value pairs -/
def toList (m : LWWMap κ α) : List (κ × α) :=
  m.entries.toList.filterMap fun (k, (v, _)) =>
    v.map fun val => (k, val)

/-- Get the size (number of present keys) -/
def size (m : LWWMap κ α) : Nat :=
  m.entries.fold (init := 0) fun acc _ (v, _) =>
    if v.isSome then acc + 1 else acc

/-- Compare Option α values for deterministic tie-breaking -/
private def compareOptionVal [Ord α] (a b : Option α) : Ordering :=
  match a, b with
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some va, some vb => compare va vb

/-- Apply an operation.
    When timestamps are equal, uses value comparison as tie-breaker for commutativity.
    (some value > none, so put wins over delete with equal timestamp) -/
def apply [Ord α] (m : LWWMap κ α) (op : LWWMapOp κ α) : LWWMap κ α :=
  match op with
  | .put key value timestamp =>
    match m.entries[key]? with
    | none =>
      { entries := m.entries.insert key (some value, timestamp) }
    | some (existingVal, existingTs) =>
      match compare timestamp existingTs with
      | .gt => { entries := m.entries.insert key (some value, timestamp) }
      | .lt => m
      | .eq =>
        -- Equal timestamps: use value comparison (some > none, so put wins over delete)
        match compareOptionVal (some value) existingVal with
        | .gt => { entries := m.entries.insert key (some value, timestamp) }
        | _ => m
  | .delete key timestamp =>
    match m.entries[key]? with
    | none =>
      { entries := m.entries.insert key (none, timestamp) }
    | some (existingVal, existingTs) =>
      match compare timestamp existingTs with
      | .gt => { entries := m.entries.insert key (none, timestamp) }
      | .lt => m
      | .eq =>
        -- Equal timestamps: use value comparison (none < some, so delete loses to put)
        match compareOptionVal none existingVal with
        | .gt => { entries := m.entries.insert key (none, timestamp) }
        | _ => m

/-- Create a put operation -/
def put (key : κ) (value : α) (timestamp : LamportTs) : LWWMapOp κ α :=
  .put key value timestamp

/-- Create a delete operation -/
def delete (key : κ) (timestamp : LamportTs) : LWWMapOp κ α :=
  .delete key timestamp

/-- Merge two maps (take entry with higher timestamp for each key).
    When timestamps are equal, uses value comparison as tie-breaker for commutativity. -/
def merge [Ord α] (a b : LWWMap κ α) : LWWMap κ α :=
  let merged := a.entries.fold (init := b.entries) fun acc key (valA, tsA) =>
    match acc[key]? with
    | none => acc.insert key (valA, tsA)
    | some (valB, tsB) =>
      match compare tsA tsB with
      | .gt => acc.insert key (valA, tsA)
      | .lt => acc
      | .eq =>
        -- Equal timestamps: use value as deterministic tie-breaker
        match compareOptionVal valA valB with
        | .gt => acc.insert key (valA, tsA)
        | .lt => acc
        | .eq => acc  -- Values equal, keep existing (either works)
  { entries := merged }

instance [Ord α] : CmRDT (LWWMap κ α) (LWWMapOp κ α) where
  empty := empty
  apply := apply
  merge := merge

instance [Ord α] : CmRDTQuery (LWWMap κ α) (LWWMapOp κ α) (List (κ × α)) where
  query := toList

instance [ToString κ] [ToString α] : ToString (LWWMap κ α) where
  toString m :=
    let pairs := m.toList.map fun (k, v) => s!"{k}: {v}"
    s!"LWWMap(\{{", ".intercalate pairs}})"

/-! ## Monadic Interface -/

/-- Put a key-value pair with timestamp in the CRDT monad -/
def putM [Ord α] (key : κ) (value : α) (timestamp : LamportTs) : CRDTM (LWWMap κ α) Unit :=
  applyM (S := LWWMap κ α) (Op := LWWMapOp κ α) (put key value timestamp)

/-- Delete a key with timestamp in the CRDT monad -/
def deleteM [Ord α] (key : κ) (timestamp : LamportTs) : CRDTM (LWWMap κ α) Unit :=
  applyM (S := LWWMap κ α) (Op := LWWMapOp κ α) (delete key timestamp)

end LWWMap

end Convergent
