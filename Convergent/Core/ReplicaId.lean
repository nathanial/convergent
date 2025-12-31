/-
  ReplicaId - Unique identifier for replicas in a distributed system

  Each replica (node/process) has a unique identifier used to:
  - Track which replica generated an operation
  - Break ties in timestamp comparisons
  - Attribute counts in vector clocks
-/
namespace Convergent

/-- Unique identifier for a replica in a distributed system -/
structure ReplicaId where
  id : Nat
  deriving BEq, Hashable, Ord, Repr, Inhabited, DecidableEq

namespace ReplicaId

/-- Create a replica ID from a natural number -/
def ofNat (n : Nat) : ReplicaId := { id := n }

instance : OfNat ReplicaId n where
  ofNat := { id := n }

instance : ToString ReplicaId where
  toString r := s!"R{r.id}"

/-- Compare two replica IDs -/
instance : LT ReplicaId where
  lt a b := a.id < b.id

instance : LE ReplicaId where
  le a b := a.id <= b.id

instance (a b : ReplicaId) : Decidable (a < b) := inferInstanceAs (Decidable (a.id < b.id))
instance (a b : ReplicaId) : Decidable (a <= b) := inferInstanceAs (Decidable (a.id <= b.id))

end ReplicaId

end Convergent
