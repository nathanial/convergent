# CLAUDE.md

## Build Commands

```bash
cd data/convergent
lake build                    # Build library
lake test                     # Run tests
lake build convergent_tests && .lake/build/bin/convergent_tests  # Run tests directly
```

## Overview

Convergent is an operation-based CRDT (CmRDT) library for Lean 4. CRDTs are data structures that can be replicated and modified independently across distributed nodes, with mathematically guaranteed conflict-free merging.

## Architecture

### Core Abstractions (`Convergent/Core/`)

- **ReplicaId** - Unique identifier for each replica/node in the system
- **Timestamp** - Lamport timestamps for total ordering, Vector clocks for causal ordering
- **UniqueId** - Globally unique IDs combining replica + sequence number
- **CmRDT** - Core typeclass defining `empty`, `apply`, and `merge` operations

### CRDTs

| Type | Module | Description |
|------|--------|-------------|
| GCounter | `Counter/GCounter` | Grow-only counter (increment only) |
| PNCounter | `Counter/PNCounter` | Positive-negative counter (inc/dec) |
| LWWRegister | `Register/LWWRegister` | Last-writer-wins register |
| MVRegister | `Register/MVRegister` | Multi-value register |
| GSet | `Set/GSet` | Grow-only set |
| TwoPSet | `Set/TwoPSet` | Two-phase set (no re-add after remove) |
| ORSet | `Set/ORSet` | Observed-remove set (supports re-add) |
| LWWMap | `Map/LWWMap` | Last-writer-wins map |
| ORMap | `Map/ORMap` | Observed-remove map with nested CRDT support |
| RGA | `Sequence/RGA` | Replicated growable array |

## Design Patterns

### Operation-based (CmRDT) Semantics

Each CRDT has:
- A **State** type holding the current value
- An **Operation** type representing mutations
- An `apply : State → Op → State` function

Operations must commute for concurrent execution:
```
apply (apply s op1) op2 = apply (apply s op2) op1
```

### Usage Pattern

```lean
-- 1. Create initial state
let state := GCounter.empty

-- 2. Create operation
let op := GCounter.increment replica

-- 3. Apply operation
let newState := GCounter.apply state op

-- 4. Query value
let value := newState.value
```

### State-based Merge

Each CRDT also provides a `merge` function for state synchronization:
```lean
let merged := GCounter.merge stateA stateB
```

### Nested CRDTs with ORMap

ORMap supports nested CRDTs as values. The third type parameter specifies the operation type for nested values:

```lean
-- Simple map (non-CRDT values use Unit for ops)
def SimpleMap := ORMap String Nat Unit

-- Nested CRDT map (each key maps to a counter)
def CounterMap := ORMap String PNCounter PNCounterOp

-- Create map with nested counter
let tag := UniqueId.new replica 1
let m := CounterMap.empty
  |> fun m => ORMap.apply m (.put "visitors" PNCounter.empty tag)
  |> fun m => ORMap.apply m (.update "visitors" tag (.increment replica))

-- Merge recursively merges nested values with matching tags
let merged := ORMap.merge replica1Map replica2Map
```

## Dependencies

- `crucible` - Test framework

## Key Files

- `Convergent.lean` - Root module, imports all CRDTs
- `Convergent/Core/CmRDT.lean` - Core typeclass
- `Convergent/Core/Timestamp.lean` - Lamport and vector clocks
- Individual CRDT implementations in subdirectories
