/-
  ORMap - Observed-Remove Map

  A map with add-wins semantics where each key can have multiple concurrent
  values. Uses unique tags to track additions, and delete only removes
  observed entries (allowing re-add with new tags).

  This combines ORSet semantics (tag-based observed-remove) with map
  key-value functionality.

  State: key → list of (value, tag) pairs
  An entry is present if it has at least one (value, tag) pair.

  Operations:
  - Put: Add a value at a key with a unique tag
  - Delete: Remove all observed tags for a key
-/
import Convergent.Core.CmRDT
import Convergent.Core.UniqueId
import Std.Data.HashMap

namespace Convergent

/-- State: key → list of (value, tag) pairs -/
structure ORMap (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  entries : Std.HashMap κ (List (α × UniqueId))
  deriving Repr, Inhabited

/-- Operation: put a value or delete observed tags -/
inductive ORMapOp (κ : Type) (α : Type) where
  | put (key : κ) (value : α) (tag : UniqueId)
  | delete (key : κ) (observedTags : List UniqueId)
  deriving Repr

namespace ORMap

variable {κ : Type} {α : Type} [BEq κ] [Hashable κ]

/-- Empty map -/
def empty : ORMap κ α := { entries := {} }

/-- Get all entries (value, tag pairs) for a key -/
def getEntries (m : ORMap κ α) (key : κ) : List (α × UniqueId) :=
  m.entries.getD key []

/-- Get all values for a key (without tags) -/
def get (m : ORMap κ α) (key : κ) : List α :=
  (m.getEntries key).map Prod.fst

/-- Get the first value for a key (convenience for single-value use) -/
def getOne (m : ORMap κ α) (key : κ) : Option α :=
  (m.getEntries key).head?.map Prod.fst

/-- Get all tags for a key -/
def getTags (m : ORMap κ α) (key : κ) : List UniqueId :=
  (m.getEntries key).map Prod.snd

/-- Check if a key is present (has at least one entry) -/
def contains (m : ORMap κ α) (key : κ) : Bool :=
  match m.entries[key]? with
  | some entries => !entries.isEmpty
  | none => false

/-- Get all keys that have at least one entry -/
def keys (m : ORMap κ α) : List κ :=
  m.entries.toList.filterMap fun (k, entries) =>
    if entries.isEmpty then none else some k

/-- Get all key-value pairs (flattened, each value separately) -/
def toList (m : ORMap κ α) : List (κ × α) :=
  m.entries.toList.flatMap fun (k, entries) =>
    entries.map fun (v, _) => (k, v)

/-- Get the number of keys with at least one entry -/
def size (m : ORMap κ α) : Nat :=
  m.entries.fold (init := 0) fun acc _ entries =>
    if entries.isEmpty then acc else acc + 1

/-- Apply an operation -/
def apply (m : ORMap κ α) (op : ORMapOp κ α) : ORMap κ α :=
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

/-- Create a put operation -/
def put (key : κ) (value : α) (tag : UniqueId) : ORMapOp κ α :=
  .put key value tag

/-- Create a delete operation that removes all currently observed tags -/
def delete (m : ORMap κ α) (key : κ) : ORMapOp κ α :=
  .delete key (m.getTags key)

/-- Merge two ORMaps (union of all entries per key) -/
def merge (a b : ORMap κ α) : ORMap κ α :=
  let merged := a.entries.fold (init := b.entries) fun acc key entriesA =>
    let entriesB := b.getEntries key
    -- Combine entries, avoiding duplicate tags
    let combined := entriesA.foldl (init := entriesB) fun entries (v, tag) =>
      if entries.any fun (_, t) => t == tag then entries
      else (v, tag) :: entries
    if combined.isEmpty then acc else acc.insert key combined
  { entries := merged }

instance : CmRDT (ORMap κ α) (ORMapOp κ α) where
  empty := empty
  apply := apply

instance [ToString κ] [ToString α] : ToString (ORMap κ α) where
  toString m :=
    let pairs := m.toList.map fun (k, v) => s!"{k}: {v}"
    s!"ORMap(\{{", ".intercalate pairs}})"

end ORMap

end Convergent
