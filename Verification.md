# CRDT Verification Status

Property-based tests using Plausible to verify CRDT laws.

## Test Coverage Matrix

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:---:|
| Merge commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge associativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Merge idempotency | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply commutativity | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Apply idempotency | n/a | n/a | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Legend: ✓ = tested and passing, ✗ = not yet tested, n/a = not applicable

## Convergence Coverage Matrix

Property: All replicas receiving the same set of operations (in any order) reach the same state.

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:---:|
| Convergence (2 ops) | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Convergence (3 ops) | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Note: 2-op convergence is covered by apply commutativity tests. 3-op tests verify forward vs reverse ordering.

## Monotonicity Coverage Matrix

Properties that values/sets only grow, never shrink.

| Property | GCounter | PNCounter | LWWReg | MVReg | GSet | TwoPSet | ORSet | LWWMap | RGA |
|----------|:--------:|:---------:|:------:|:-----:|:----:|:-------:|:-----:|:------:|:---:|
| Value never decreases | ✗ | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |
| Elements never removed | n/a | n/a | n/a | n/a | ✗ | n/a | n/a | n/a | n/a |
| Added set never shrinks | n/a | n/a | n/a | n/a | n/a | ✗ | n/a | n/a | n/a |
| Removed set never shrinks | n/a | n/a | n/a | n/a | n/a | ✗ | n/a | n/a | n/a |

## Type-Specific Semantics Coverage Matrix

Behavioral properties unique to each CRDT type.

| Property | Applicable CRDTs | Status |
|----------|------------------|:------:|
| Later timestamp wins | LWWReg, LWWMap | ✗ |
| Dominated values removed | MVReg | ✗ |
| Concurrent values preserved | MVReg | ✗ |
| Re-add after remove works | ORSet | ✗ |
| Remove-then-add is add | ORSet | ✗ |
| Removed cannot re-add | TwoPSet | ✗ |
| Insert ordering preserved | RGA | ✗ |
| Delete creates tombstone | RGA | ✗ |
| Increment adds exactly 1 | GCounter | ✗ |
| Inc/dec are inverses | PNCounter | ✗ |

## Test Files

- `ConvergentTests/PropertyTests.lean` - Plausible property tests
- `ConvergentTests/CounterTests.lean` - GCounter, PNCounter unit tests
- `ConvergentTests/RegisterTests.lean` - LWWRegister, MVRegister unit tests
- `ConvergentTests/SetTests.lean` - GSet, TwoPSet, ORSet unit tests
- `ConvergentTests/MapTests.lean` - LWWMap unit tests
- `ConvergentTests/SequenceTests.lean` - RGA unit tests

## Running Tests

```bash
lake build && lake test
```
