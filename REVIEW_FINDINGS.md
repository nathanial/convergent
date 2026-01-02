# Convergent Review Findings (Jan 2, 2026)

## Status Update (Jan 2, 2026)

Resolved:

1) MVRegister merge ordering is now canonical (sorted clock entries, no `toString`).
   Equivalent clocks yield a deterministic winner, and the new test passes.
   - `data/convergent/Convergent/Register/MVRegister.lean`
   - `data/convergent/ConvergentTests/RegisterTests.lean`

2) RGA ordering now respects `afterId` links instead of global ID sorting.
   Nodes carry `afterId`, ordering is derived from the after-link tree with
   deterministic sibling ordering, and the new ordering test passes.
   - `data/convergent/Convergent/Sequence/RGA.lean`
   - `data/convergent/ConvergentTests/SequenceTests.lean`

3) Added state-level property checks for ORSet/ORMap/LWWMap/MVRegister (with
   ORMap well-formed/compatibility guards).
   - `data/convergent/ConvergentTests/PropertyTests.lean`

Open:

4) Medium — “trivial” `CmRDT` instances for `Nat/Int/String/Bool` use left-biased `merge`,
   which is non-commutative. ORMap merges values by `CmRDT.merge` for matching tags, so
   a tag that diverges (e.g., via `.update`) can violate CRDT laws. Safe only if those
   instances are never used where a tag can evolve.
   - `data/convergent/Convergent/Core/CmRDT.lean:55-73`
   - `data/convergent/Convergent/Map/ORMap.lean:124-137`

5) Low — `Fugue.traverse` and `isAncestor` are `partial` and assume an acyclic parent graph.
   Malformed ops (cycles/self-parent) can cause non-termination. If ops can be untrusted,
   add validation or cycle protection.
   - `data/convergent/Convergent/Sequence/Fugue.lean:152-197`

## Notes

- RGA serialization format changed: `RGANode` now encodes `afterId`. This is a breaking
  change if you have stored RGA data. See `data/convergent/Convergent/Serialization/Sequence.lean`.
