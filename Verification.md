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

## Other Properties Not Yet Tested

### Convergence
All replicas receiving the same set of operations (in any order) should reach the same state.

### Monotonicity
- GCounter: value never decreases
- GSet: elements never removed
- TwoPSet: added/removed sets never shrink

### Type-Specific Semantics
- ORSet: can re-add after remove with new tag
- LWW types: later timestamps always win
- MVRegister: vector clock causality (dominated values removed)

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
