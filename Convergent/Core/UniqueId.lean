/-
  UniqueId - Globally unique identifiers for operations

  Used by CRDTs that need to uniquely identify operations or elements,
  such as OR-Set (to tag additions) and RGA (to identify list elements).

  A UniqueId combines a replica ID with a local sequence number,
  guaranteeing global uniqueness as long as each replica maintains
  its own monotonically increasing sequence.
-/
import Convergent.Core.ReplicaId

namespace Convergent

/-- Globally unique identifier combining replica ID and local sequence number -/
structure UniqueId where
  replica : ReplicaId
  seq : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

namespace UniqueId

/-- Create a unique ID -/
def new (replica : ReplicaId) (seq : Nat) : UniqueId := { replica, seq }

/-- Total ordering for deterministic behavior -/
instance : Ord UniqueId where
  compare a b :=
    match compare a.replica b.replica with
    | .eq => compare a.seq b.seq
    | other => other

instance : LT UniqueId where
  lt a b := match Ord.compare a b with
    | .lt => True
    | _ => False

instance : LE UniqueId where
  le a b := match Ord.compare a b with
    | .gt => False
    | _ => True

instance (a b : UniqueId) : Decidable (a < b) :=
  match h : Ord.compare a b with
  | .lt => isTrue (by simp only [LT.lt]; rw [h]; trivial)
  | .eq => isFalse (by simp only [LT.lt]; rw [h]; intro h; cases h)
  | .gt => isFalse (by simp only [LT.lt]; rw [h]; intro h; cases h)

instance (a b : UniqueId) : Decidable (a <= b) :=
  match h : Ord.compare a b with
  | .lt => isTrue (by simp only [LE.le]; rw [h]; trivial)
  | .eq => isTrue (by simp only [LE.le]; rw [h]; trivial)
  | .gt => isFalse (by simp only [LE.le]; rw [h]; intro h; cases h)

instance : ToString UniqueId where
  toString uid := s!"{uid.replica}.{uid.seq}"

end UniqueId

/-- Generator for unique IDs within a single replica -/
structure UniqueIdGen where
  replica : ReplicaId
  nextSeq : Nat
  deriving Repr, Inhabited

namespace UniqueIdGen

/-- Create a new generator for a replica -/
def init (replica : ReplicaId) : UniqueIdGen :=
  { replica, nextSeq := 0 }

/-- Generate the next unique ID -/
def next (gen : UniqueIdGen) : UniqueId × UniqueIdGen :=
  let uid := UniqueId.new gen.replica gen.nextSeq
  let gen' := { gen with nextSeq := gen.nextSeq + 1 }
  (uid, gen')

end UniqueIdGen

end Convergent
