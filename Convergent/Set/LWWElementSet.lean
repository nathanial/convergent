/-
  LWWElementSet - Last-Writer-Wins Element Set

  A set with per-element timestamp-based conflict resolution.
  Each element tracks when it was last added or removed, and
  the operation with the highest timestamp wins.

  Unlike TwoPSet, elements can be re-added after removal.
  Unlike ORSet, conflict resolution is timestamp-based rather than tag-based.

  State: Maps each element to (isPresent, timestamp).
  - isPresent = true: element is in the set (last op was add)
  - isPresent = false: element is not in set (last op was remove)

  Operations:
  - Add: Add element with timestamp
  - Remove: Remove element with timestamp
-/
import Convergent.Core.CmRDT
import Convergent.Core.Monad
import Convergent.Core.Timestamp
import Std.Data.HashMap

namespace Convergent

/-- State: element → (isPresent, timestamp) -/
structure LWWElementSet (α : Type) [BEq α] [Hashable α] where
  entries : Std.HashMap α (Bool × LamportTs)
  deriving Repr, Inhabited

/-- Operation: add or remove with timestamp -/
inductive LWWElementSetOp (α : Type) where
  | add (value : α) (timestamp : LamportTs)
  | remove (value : α) (timestamp : LamportTs)
  deriving Repr

namespace LWWElementSet

variable {α : Type} [BEq α] [Hashable α]

/-- Empty set -/
def empty : LWWElementSet α := { entries := {} }

/-- Check if an element is in the set -/
def contains (set : LWWElementSet α) (value : α) : Bool :=
  match set.entries[value]? with
  | some (present, _) => present
  | none => false

/-- Get the timestamp for an element (if it exists in entries) -/
def getTimestamp (set : LWWElementSet α) (value : α) : Option LamportTs :=
  set.entries[value]?.map Prod.snd

/-- Get all elements currently in the set -/
def toList (set : LWWElementSet α) : List α :=
  set.entries.toList.filterMap fun (elem, (present, _)) =>
    if present then some elem else none

/-- Get the size of the set -/
def size (set : LWWElementSet α) : Nat :=
  set.entries.fold (init := 0) fun acc _ (present, _) =>
    if present then acc + 1 else acc

/-- Helper: Apply an operation with a given presence flag.
    When timestamps are equal, add-wins (bias towards presence). -/
private def applyEntry (set : LWWElementSet α) (value : α) (isAdd : Bool) (ts : LamportTs)
    : LWWElementSet α :=
  match set.entries[value]? with
  | none =>
    { entries := set.entries.insert value (isAdd, ts) }
  | some (existingPresent, existingTs) =>
    match compare ts existingTs with
    | .gt =>
      { entries := set.entries.insert value (isAdd, ts) }
    | .lt => set
    | .eq =>
      -- Equal timestamps: add-wins (bias towards presence)
      -- If isAdd = true, always set to true
      -- If isAdd = false (remove), keep existing state
      if isAdd && !existingPresent then
        { entries := set.entries.insert value (true, ts) }
      else
        set

/-- Apply an operation -/
def apply (set : LWWElementSet α) (op : LWWElementSetOp α) : LWWElementSet α :=
  match op with
  | .add value ts => applyEntry set value true ts
  | .remove value ts => applyEntry set value false ts

/-- Create an add operation -/
def add (value : α) (timestamp : LamportTs) : LWWElementSetOp α :=
  .add value timestamp

/-- Create a remove operation -/
def remove (value : α) (timestamp : LamportTs) : LWWElementSetOp α :=
  .remove value timestamp

/-- Merge two sets (take entry with higher timestamp for each element).
    When timestamps are equal, add-wins (bias towards presence). -/
def merge (a b : LWWElementSet α) : LWWElementSet α :=
  let merged := a.entries.fold (init := b.entries) fun acc elem (presentA, tsA) =>
    match acc[elem]? with
    | none => acc.insert elem (presentA, tsA)
    | some (presentB, tsB) =>
      match compare tsA tsB with
      | .gt => acc.insert elem (presentA, tsA)
      | .lt => acc
      | .eq =>
        -- Equal timestamps: add-wins (bias towards presence)
        if presentA || presentB then
          acc.insert elem (true, tsA)
        else
          acc  -- Both false, keep existing
  { entries := merged }

instance : CmRDT (LWWElementSet α) (LWWElementSetOp α) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (LWWElementSet α) (LWWElementSetOp α) (List α) where
  query := toList

instance [ToString α] : ToString (LWWElementSet α) where
  toString set :=
    let elems := set.toList.map toString
    s!"LWWElementSet(\{{", ".intercalate elems}})"

/-! ## Monadic Interface -/

/-- Add an element with timestamp in the CRDT monad -/
def addM (value : α) (timestamp : LamportTs) : CRDTM (LWWElementSet α) Unit :=
  applyM (add value timestamp)

/-- Remove an element with timestamp in the CRDT monad -/
def removeM (value : α) (timestamp : LamportTs) : CRDTM (LWWElementSet α) Unit :=
  applyM (remove value timestamp)

end LWWElementSet

end Convergent
