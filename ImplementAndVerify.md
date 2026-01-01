# CRDT Implementation and Verification Status

## Implementation Status

### Counters

| CRDT | Status | Description |
|------|:------:|-------------|
| GCounter | ✓ | Grow-only counter (increment only) |
| PNCounter | ✓ | Positive-negative counter (increment/decrement) |

### Registers

| CRDT | Status | Description |
|------|:------:|-------------|
| LWWRegister | ✓ | Last-writer-wins register (timestamp resolves conflicts) |
| MVRegister | ✓ | Multi-value register (preserves concurrent writes) |

### Sets

| CRDT | Status | Description |
|------|:------:|-------------|
| GSet | ✓ | Grow-only set (add only, no remove) |
| TwoPSet | ✓ | Two-phase set (remove is permanent) |
| ORSet | ✓ | Observed-remove set (add-wins, supports re-add) |
| LWWElementSet | ✓ | Set with per-element timestamps |

### Maps

| CRDT | Status | Description |
|------|:------:|-------------|
| LWWMap | ✓ | Last-writer-wins map |
| ORMap | ✓ | Observed-remove map (add-wins, supports re-add) |
| PNMap | ✓ | Map with PNCounter values |

### Sequences

| CRDT | Status | Description |
|------|:------:|-------------|
| RGA | ✓ | Replicated growable array |
| LSEQ | ✓ | Adaptive allocation sequence CRDT (position-based) |
| Fugue | ✓ | Tree-based text CRDT with maximal non-interleaving |
| Logoot | ✗ | Position-based sequence CRDT |

### Flags

| CRDT | Status | Description |
|------|:------:|-------------|
| EWFlag | ✓ | Enable-wins flag (concurrent enable + disable = enabled) |
| DWFlag | ✓ | Disable-wins flag (concurrent enable + disable = disabled) |

### Graphs

| CRDT | Status | Description |
|------|:------:|-------------|
| TwoPGraph | ✓ | Two-phase graph (vertices and edges are TwoPSets) |
| AddOnlyDAG | ✗ | Add-only directed acyclic graph |

---

## Test Coverage Matrices

### Core CRDT Laws

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWElemSet | LWWMap | ORMap | PNMap | RGA | LSEQ | Fugue | EWFlag | DWFlag | TwoPGraph |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:----------:|:------:|:-----:|:-----:|:---:|:----:|:-----:|:------:|:------:|:---------:|
| Merge commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge associativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge idempotency | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply idempotency | n/a | n/a | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | n/a | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Legend: ✓ = tested and passing, ✗ = not yet tested, n/a = not applicable

### Convergence

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWElemSet | LWWMap | ORMap | PNMap | RGA | LSEQ | Fugue | EWFlag | DWFlag | TwoPGraph |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:----------:|:------:|:-----:|:-----:|:---:|:----:|:-----:|:------:|:------:|:---------:|
| 2-op convergence | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| 3-op convergence | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Note: 2-op convergence covered by apply commutativity. 3-op tests forward vs reverse ordering.

### Monotonicity

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | ORMap | RGA | LSEQ |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:-----:|:---:|:----:|
| Value never decreases | ✓ | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |
| Elements never removed | n/a | n/a | n/a | n/a | ✓ | n/a | n/a | n/a | n/a | n/a | n/a |
| Added set never shrinks | n/a | n/a | n/a | n/a | n/a | ✓ | n/a | n/a | n/a | n/a | n/a |
| Removed set never shrinks | n/a | n/a | n/a | n/a | n/a | ✓ | n/a | n/a | n/a | n/a | n/a |

### Type-Specific Semantics

| Property | Applicable CRDTs | Status |
|----------|------------------|:------:|
| Later timestamp wins | LWWReg, LWWMap | ✓ |
| Dominated values removed | MVReg | ✓ |
| Concurrent values preserved | MVReg | ✓ |
| Re-add after remove works | ORSet, ORMap | ✓ |
| Remove-then-add is add | ORSet | ✓ |
| Removed cannot re-add | TwoPSet | ✓ |
| Insert ordering preserved | RGA, LSEQ, Fugue | ✓ |
| Delete creates tombstone | RGA, LSEQ, Fugue | ✓ |
| Contains ID after insert | LSEQ, Fugue | ✓ |
| Delete makes invisible but keeps ID | Fugue | ✓ |
| Increment adds exactly 1 | GCounter | ✓ |
| Inc/dec work correctly | PNCounter | ✓ |
| Contains key after put | ORMap | ✓ |
| Get returns value after put | ORMap | ✓ |
| Enable-wins (concurrent = enabled) | EWFlag | ✓ |
| Disable-wins (concurrent = disabled) | DWFlag | ✓ |
| Later timestamp wins per element | LWWElementSet | ✓ |
| Can re-add after remove | LWWElementSet | ✓ |
| Add contains element | LWWElementSet | ✓ |
| Increment adds exactly 1 | PNMap | ✓ |
| Decrement subtracts exactly 1 | PNMap | ✓ |
| Contains vertex after add | TwoPGraph | ✓ |
| Vertex removed after remove | TwoPGraph | ✓ |
| Once vertex removed, cannot re-add | TwoPGraph | ✓ |
| Contains edge after add (with endpoints) | TwoPGraph | ✓ |
| Edge removed after remove | TwoPGraph | ✓ |
| Once edge removed, cannot re-add | TwoPGraph | ✓ |
| Vertex removal hides edges | TwoPGraph | ✓ |

---

## Test Summary

**Total Tests: 322** (154 unit/scenario + 168 property)

### Unit and Scenario Tests: 154
- Counter tests: 10
- Register tests: 9
- Set tests: 24
- Map tests: 28
- Sequence tests: 31 (RGA, LSEQ, Fugue)
- Flag tests: 15
- Graph tests: 13
- Scenario tests: 24 (real-world usage examples)

### Property Tests: 168
- Core CRDT laws: 51 tests (merge laws) + 17 tests (apply commutativity) + 25 tests (apply idempotency)
- Convergence: 17 tests (3-op)
- Monotonicity: 4 tests
- Type-specific: 32 tests (includes EWFlag/DWFlag/LWWElementSet/PNMap/LSEQ/Fugue/TwoPGraph semantics)
- Additional semantics: 22 tests

---

## Future CRDTs - Expected Properties

When implementing new CRDTs, they should satisfy:

### All CRDTs
- [ ] Merge commutativity
- [ ] Merge associativity
- [ ] Merge idempotency
- [ ] Apply commutativity

### EWFlag / DWFlag (Implemented ✓)
- [x] Apply idempotency
- [x] Enable-wins (EWFlag): concurrent enable + disable = enabled
- [x] Disable-wins (DWFlag): concurrent enable + disable = disabled

### LWWElementSet (Implemented ✓)
- [x] Apply idempotency
- [x] Later timestamp wins per element
- [x] Can remove and re-add same element

### LSEQ (Implemented ✓)
- [x] Apply idempotency (insert/delete)
- [x] Insert ordering preserved (lexicographic by position ID)
- [x] Delete creates tombstone
- [x] Contains ID after insert

### TwoPGraph (Implemented ✓)
- [x] Apply idempotency (add/remove vertex/edge)
- [x] Contains vertex after add
- [x] Vertex removed after remove
- [x] Once vertex removed, cannot re-add (two-phase semantics)
- [x] Contains edge after add (when both endpoints exist)
- [x] Edge removed after remove
- [x] Once edge removed, cannot re-add
- [x] Vertex removal hides edges

---

## Running Tests

```bash
lake build && lake test
```

## Test Files

- `ConvergentTests/PropertyTests.lean` - Plausible property tests (168 tests)
- `ConvergentTests/ScenarioTests.lean` - Real-world usage scenarios (24 tests)
- `ConvergentTests/CounterTests.lean` - GCounter, PNCounter unit tests
- `ConvergentTests/RegisterTests.lean` - LWWRegister, MVRegister unit tests
- `ConvergentTests/SetTests.lean` - GSet, TwoPSet, ORSet, LWWElementSet unit tests
- `ConvergentTests/MapTests.lean` - LWWMap, ORMap, PNMap unit tests
- `ConvergentTests/SequenceTests.lean` - RGA, LSEQ, Fugue unit tests
- `ConvergentTests/FlagTests.lean` - EWFlag, DWFlag unit tests
- `ConvergentTests/GraphTests.lean` - TwoPGraph unit tests

### Scenario Tests

The `ScenarioTests.lean` file contains practical usage examples:

| Scenario | CRDT | Description |
|----------|------|-------------|
| Shopping Cart | ORSet | Multi-device cart with concurrent add/remove |
| Like Button | GCounter | Multi-region counting with merge |
| User Presence | EWFlag | Online/offline status across devices |
| Leaderboard | LWWMap | Player scores with timestamp resolution |
| Social Network | TwoPGraph | Friend relationships, unfriend, account deletion |
| Inventory System | PNMap | Multi-warehouse stock tracking |
| Collaborative Text | Fugue | Concurrent typing with non-interleaving |
| Conflict Resolution | MVRegister | Preserving concurrent edits |
| Feature Flags | LWWElementSet | Per-element timestamp management |
