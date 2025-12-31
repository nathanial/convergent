# CRDT Implementation and Verification Status

## Implementation Status

### Counters

| CRDT | Status | Description |
|------|:------:|-------------|
| GCounter | ✓ | Grow-only counter (increment only) |
| PNCounter | ✓ | Positive-negative counter (increment/decrement) |
| BoundedCounter | ✗ | Counter with min/max bounds |

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
| LWWElementSet | ✗ | Set with per-element timestamps |

### Maps

| CRDT | Status | Description |
|------|:------:|-------------|
| LWWMap | ✓ | Last-writer-wins map |
| ORMap | ✓ | Observed-remove map (add-wins, supports re-add) |
| PNMap | ✗ | Map with PNCounter values |

### Sequences

| CRDT | Status | Description |
|------|:------:|-------------|
| RGA | ✓ | Replicated growable array |
| Logoot | ✗ | Position-based sequence CRDT |
| LSEQ | ✗ | Adaptive allocation sequence CRDT |

### Flags

| CRDT | Status | Description |
|------|:------:|-------------|
| EWFlag | ✗ | Enable-wins flag (concurrent enable + disable = enabled) |
| DWFlag | ✗ | Disable-wins flag (concurrent enable + disable = disabled) |

### Graphs

| CRDT | Status | Description |
|------|:------:|-------------|
| 2P2PGraph | ✗ | Two-phase graph (vertices and edges) |
| AddOnlyDAG | ✗ | Add-only directed acyclic graph |

---

## Test Coverage Matrices

### Core CRDT Laws

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | ORMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:-----:|:---:|
| Merge commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge associativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge idempotency | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply idempotency | n/a | n/a | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Legend: ✓ = tested and passing, ✗ = not yet tested, n/a = not applicable

### Convergence

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | ORMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:-----:|:---:|
| 2-op convergence | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| 3-op convergence | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Note: 2-op convergence covered by apply commutativity. 3-op tests forward vs reverse ordering.

### Monotonicity

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | ORMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:-----:|:---:|
| Value never decreases | ✓ | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |
| Elements never removed | n/a | n/a | n/a | n/a | ✓ | n/a | n/a | n/a | n/a | n/a |
| Added set never shrinks | n/a | n/a | n/a | n/a | n/a | ✓ | n/a | n/a | n/a | n/a |
| Removed set never shrinks | n/a | n/a | n/a | n/a | n/a | ✓ | n/a | n/a | n/a | n/a |

### Type-Specific Semantics

| Property | Applicable CRDTs | Status |
|----------|------------------|:------:|
| Later timestamp wins | LWWReg, LWWMap | ✓ |
| Dominated values removed | MVReg | ✓ |
| Concurrent values preserved | MVReg | ✓ |
| Re-add after remove works | ORSet, ORMap | ✓ |
| Remove-then-add is add | ORSet | ✓ |
| Removed cannot re-add | TwoPSet | ✓ |
| Insert ordering preserved | RGA | ✓ |
| Delete creates tombstone | RGA | ✓ |
| Increment adds exactly 1 | GCounter | ✓ |
| Inc/dec work correctly | PNCounter | ✓ |
| Contains key after put | ORMap | ✓ |
| Get returns value after put | ORMap | ✓ |

---

## Test Summary

**Total Property Tests: 88**

- Core CRDT laws: 30 tests (merge laws) + 10 tests (apply commutativity) + 13 tests (apply idempotency)
- Convergence: 10 tests (3-op)
- Monotonicity: 4 tests
- Type-specific: 13 tests
- Additional semantics: 8 tests

---

## Future CRDTs - Expected Properties

When implementing new CRDTs, they should satisfy:

### All CRDTs
- [ ] Merge commutativity
- [ ] Merge associativity
- [ ] Merge idempotency
- [ ] Apply commutativity

### EWFlag / DWFlag
- [ ] Apply idempotency
- [ ] Enable-wins (EWFlag): concurrent enable + disable = enabled
- [ ] Disable-wins (DWFlag): concurrent enable + disable = disabled

### BoundedCounter
- [ ] Value stays within bounds
- [ ] Increment at max is no-op
- [ ] Decrement at min is no-op

### LWWElementSet
- [ ] Apply idempotency
- [ ] Later timestamp wins per element
- [ ] Can remove and re-add same element

---

## Running Tests

```bash
lake build && lake test
```

## Test Files

- `ConvergentTests/PropertyTests.lean` - Plausible property tests (78 tests)
- `ConvergentTests/CounterTests.lean` - GCounter, PNCounter unit tests
- `ConvergentTests/RegisterTests.lean` - LWWRegister, MVRegister unit tests
- `ConvergentTests/SetTests.lean` - GSet, TwoPSet, ORSet unit tests
- `ConvergentTests/MapTests.lean` - LWWMap unit tests
- `ConvergentTests/SequenceTests.lean` - RGA unit tests
