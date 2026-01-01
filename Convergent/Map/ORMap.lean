/-
  ORMap - Observed-Remove Map with Nested CRDT Support

  A map with add-wins semantics where each key can have multiple concurrent
  values. Uses unique tags to track additions, and delete only removes
  observed entries (allowing re-add with new tags).

  This combines ORSet semantics (tag-based observed-remove) with map
  key-value functionality, and supports nested CRDTs as values.

  State: key → list of (value, tag) pairs
  An entry is present if it has at least one (value, tag) pair.

  Operations:
  - Put: Add a value at a key with a unique tag
  - Delete: Remove all observed tags for a key
  - Update: Apply a nested CRDT operation to a value at a specific tag
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.UniqueId
import Std.Data.HashMap

namespace Convergent

/-- State: key → list of (value, tag) pairs -/
structure ORMap (κ : Type) (α : Type) (OpA : Type) [BEq κ] [Hashable κ] where
  entries : Std.HashMap κ (List (α × UniqueId))
  deriving Repr, Inhabited

/-- Operation: put a value, delete observed tags, or update a nested value -/
inductive ORMapOp (κ : Type) (α : Type) (OpA : Type) where
  | put (key : κ) (value : α) (tag : UniqueId)
  | delete (key : κ) (observedTags : List UniqueId)
  | update (key : κ) (tag : UniqueId) (op : OpA)
  deriving Repr

namespace ORMap

variable {κ : Type} {α : Type} {OpA : Type} [BEq κ] [Hashable κ]

/-- Empty map -/
def empty : ORMap κ α OpA := { entries := {} }

/-- Get all entries (value, tag pairs) for a key -/
def getEntries (m : ORMap κ α OpA) (key : κ) : List (α × UniqueId) :=
  m.entries.getD key []

/-- Get all values for a key (without tags) -/
def get (m : ORMap κ α OpA) (key : κ) : List α :=
  (m.getEntries key).map Prod.fst

/-- Get the first value for a key (convenience for single-value use) -/
def getOne (m : ORMap κ α OpA) (key : κ) : Option α :=
  (m.getEntries key).head?.map Prod.fst

/-- Get all tags for a key -/
def getTags (m : ORMap κ α OpA) (key : κ) : List UniqueId :=
  (m.getEntries key).map Prod.snd

/-- Check if a key is present (has at least one entry) -/
def contains (m : ORMap κ α OpA) (key : κ) : Bool :=
  match m.entries[key]? with
  | some entries => !entries.isEmpty
  | none => false

/-- Get all keys that have at least one entry -/
def keys (m : ORMap κ α OpA) : List κ :=
  m.entries.toList.filterMap fun (k, entries) =>
    if entries.isEmpty then none else some k

/-- Get all key-value pairs (flattened, each value separately) -/
def toList (m : ORMap κ α OpA) : List (κ × α) :=
  m.entries.toList.flatMap fun (k, entries) =>
    entries.map fun (v, _) => (k, v)

/-- Get the number of keys with at least one entry -/
def size (m : ORMap κ α OpA) : Nat :=
  m.entries.fold (init := 0) fun acc _ entries =>
    if entries.isEmpty then acc else acc + 1

/-- Apply an operation -/
def apply [CmRDT α OpA] (m : ORMap κ α OpA) (op : ORMapOp κ α OpA) : ORMap κ α OpA :=
  match op with
  | .put key value tag =>
    let currentEntries := m.getEntries key
    -- Check if this tag already exists (idempotency)
    if currentEntries.any fun (_, t) => t == tag then m
    else { entries := m.entries.insert key ((value, tag) :: currentEntries) }
  | .delete key observedTags =>
    match m.entries[key]? with
    | none => m
    | some currentEntries =>
      let remainingEntries := currentEntries.filter fun (_, tag) =>
        !observedTags.any (· == tag)
      if remainingEntries.isEmpty then
        { entries := m.entries.erase key }
      else
        { entries := m.entries.insert key remainingEntries }
  | .update key tag nestedOp =>
    -- Find entry with matching tag and apply the nested operation
    match m.entries[key]? with
    | none => m  -- Key doesn't exist, no-op
    | some currentEntries =>
      let hasTag := currentEntries.any fun (_, t) => t == tag
      if !hasTag then m  -- Tag doesn't exist, no-op
      else
        let updatedEntries := currentEntries.map fun (v, t) =>
          if t == tag then (CmRDT.apply v nestedOp, t) else (v, t)
        { entries := m.entries.insert key updatedEntries }

/-- Create a put operation -/
def put (key : κ) (value : α) (tag : UniqueId) : ORMapOp κ α OpA :=
  .put key value tag

/-- Create a delete operation that removes all currently observed tags -/
def delete (m : ORMap κ α OpA) (key : κ) : ORMapOp κ α OpA :=
  .delete key (m.getTags key)

/-- Create an update operation to apply a nested op to a value at a specific tag -/
def update (key : κ) (tag : UniqueId) (op : OpA) : ORMapOp κ α OpA :=
  .update key tag op

/-- Merge two ORMaps with recursive merge for nested CRDTs.
    For each key, combines entries. When the same tag appears in both maps,
    the nested values are merged using CmRDT.merge. -/
def merge [inst : CmRDT α OpA] (a b : ORMap κ α OpA) : ORMap κ α OpA :=
  let merged := a.entries.fold (init := b.entries) fun acc key entriesA =>
    let entriesB := b.getEntries key
    -- Combine entries with recursive merge for matching tags
    let combined := entriesA.foldl (init := entriesB) fun entries (vA, tagA) =>
      match entries.find? fun (_, t) => t == tagA with
      | some (vB, _) =>
        -- Same tag exists in both - merge the values
        let mergedValue := inst.merge vA vB
        entries.map fun (v, t) =>
          if t == tagA then (mergedValue, t) else (v, t)
      | none =>
        -- Tag only in A, add it
        (vA, tagA) :: entries
    if combined.isEmpty then acc else acc.insert key combined
  { entries := merged }

instance [CmRDT α OpA] : CmRDT (ORMap κ α OpA) (ORMapOp κ α OpA) where
  empty := empty
  apply := apply
  merge := merge

instance [CmRDT α OpA] : CmRDTQuery (ORMap κ α OpA) (ORMapOp κ α OpA) (List (κ × α)) where
  query := toList

instance [ToString κ] [ToString α] : ToString (ORMap κ α OpA) where
  toString m :=
    let pairs := m.toList.map fun (k, v) => s!"{k}: {v}"
    s!"ORMap(\{{", ".intercalate pairs}})"

/-! ## Monadic Interface -/

/-- Put a value at a key with a unique tag in the CRDT monad -/
def putM [CmRDT α OpA] (key : κ) (value : α) (tag : UniqueId) : CRDTM (ORMap κ α OpA) Unit :=
  applyM (S := ORMap κ α OpA) (Op := ORMapOp κ α OpA) (put key value tag)

/-- Delete a key with its observed tags in the CRDT monad -/
def deleteWithTagsM [CmRDT α OpA] (key : κ) (observedTags : List UniqueId) : CRDTM (ORMap κ α OpA) Unit :=
  applyM (S := ORMap κ α OpA) (Op := ORMapOp κ α OpA) (ORMapOp.delete key observedTags)

/-- Update a nested value at a key/tag in the CRDT monad -/
def updateM [CmRDT α OpA] (key : κ) (tag : UniqueId) (op : OpA) : CRDTM (ORMap κ α OpA) Unit :=
  applyM (S := ORMap κ α OpA) (Op := ORMapOp κ α OpA) (update key tag op)

end ORMap

end Convergent
