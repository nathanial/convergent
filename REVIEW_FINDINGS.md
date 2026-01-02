# Convergent Review Findings (Jan 2, 2026)

## Findings

1) High — MVRegister merge ordering uses `compare (toString a) (toString b)` for vector clocks.
   `VectorClock.toString` depends on `HashMap.toList` order, which is non-canonical.
   Equivalent clocks built with different insertion orders can compare differently,
   changing which value survives when clocks are equivalent and breaking commutativity
   across replicas.
   - `data/convergent/Convergent/Register/MVRegister.lean:101-126`
   - `data/convergent/Convergent/Core/Timestamp.lean:120-122`

2) Medium — `RGA.apply` sorts by `id` after `insertAfter`, so final ordering is effectively
   `UniqueId` order, not “insert after” order. Inserts with an `id` that sorts before
   the target can move ahead of their intended position, which conflicts with the RGA
   spec in module docs.
   - `data/convergent/Convergent/Sequence/RGA.lean:90-138`

3) Medium — “trivial” `CmRDT` instances for `Nat/Int/String/Bool` use left-biased `merge`,
   which is non-commutative. ORMap merges values by `CmRDT.merge` for matching tags, so
   a tag that diverges (e.g., via `.update`) can violate CRDT laws. Safe only if those
   instances are never used where a tag can evolve.
   - `data/convergent/Convergent/Core/CmRDT.lean:55-73`
   - `data/convergent/Convergent/Map/ORMap.lean:124-137`

4) Low — `Fugue.traverse` and `isAncestor` are `partial` and assume an acyclic parent graph.
   Malformed ops (cycles/self-parent) can cause non-termination. If ops can be untrusted,
   add validation or cycle protection.
   - `data/convergent/Convergent/Sequence/Fugue.lean:152-197`

## Missing Tests

1) MVRegister: determinism when two vector clocks are logically equal but built in different
   insertion orders and paired with different values; the expected tie-breaker should be
   stable. This should fail with the current `toString` comparator.

2) RGA: ordering test where `afterId` conflicts with `UniqueId` order (e.g., insert `id2`
   after `id1` where `id2 < id1`) to confirm intended semantics.

3) Property tests: state-level equivalence for ORSet/ORMap/LWWMap/MVRegister
   (tags/timestamps/clocks), not just query values, since metadata affects future ops.
   Current equality helpers can miss divergence.

4) Optional (if canonical bytes matter): serialization determinism for HashMap/VectorClock
   contents built in different insertion orders.

