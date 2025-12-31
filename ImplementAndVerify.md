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
| ORMap | ✗ | Observed-remove map (nested CRDT composition) |
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

## Test Coverage Matrix

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:---:|
| **Core CRDT Laws** |
| Merge commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge associativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge idempotency | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply idempotency | · | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Convergence** |
| 2-op convergence | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| 3-op convergence | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Monotonicity** |
| Value never decreases | ✓ | · | · | · | · | · | · | · | · |
| Elements never removed | · | · | · | · | ✓ | · | · | · | · |
| Added set never shrinks | · | · | · | · | · | ✓ | · | · | · |
| Removed set never shrinks | · | · | · | · | · | ✓ | · | · | · |
| **Type-Specific Semantics** |
| Later timestamp wins | · | · | ✓ | · | · | · | · | ✓ | · |
| Dominated values removed | · | · | · | ✓ | · | · | · | · | · |
| Concurrent values preserved | · | · | · | ✓ | · | · | · | · | · |
| Re-add after remove works | · | · | · | · | · | · | ✓ | · | · |
| Remove-then-add is add | · | · | · | · | · | · | ✓ | · | · |
| Removed cannot re-add | · | · | · | · | · | ✓ | · | · | · |
| Insert ordering preserved | · | · | · | · | · | · | · | · | ✓ |
| Delete creates tombstone | · | · | · | · | · | · | · | · | ✓ |
| Increment adds exactly 1 | ✓ | · | · | · | · | · | · | · | · |
| Inc/dec work correctly | · | ✓ | · | · | · | · | · | · | · |

Legend: ✓ = tested, · = not applicable

---

## Test Summary

**Total Property Tests: 78**

- Core CRDT laws: 27 tests (merge laws) + 9 tests (apply commutativity) + 11 tests (apply idempotency)
- Convergence: 9 tests (3-op)
- Monotonicity: 4 tests
- Type-specific: 10 tests
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

### ORMap
- [ ] Apply idempotency
- [ ] Nested CRDT operations commute
- [ ] Remove key then update = update (add-wins)

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
