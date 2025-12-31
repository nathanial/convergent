# Convergent

Operation-based CRDTs (Conflict-free Replicated Data Types) for Lean 4.

## What are CRDTs?

CRDTs are data structures designed for distributed systems that allow:
- Replication across multiple nodes
- Independent local modifications
- Automatic conflict-free merging

This library implements **operation-based CRDTs** (CmRDTs) where replicas exchange operations rather than full state.

## Installation

Add to your `lakefile.lean`:

```lean
require convergent from git "https://github.com/nathanial/convergent" @ "v0.1.0"
```

## Available CRDTs

### Counters
- **GCounter** - Grow-only counter (can only increment)
- **PNCounter** - Supports both increment and decrement

### Registers
- **LWWRegister** - Single value, last write wins by timestamp
- **MVRegister** - Preserves all concurrent writes

### Sets
- **GSet** - Grow-only set (add only)
- **TwoPSet** - Add and remove, but once removed an element cannot be re-added
- **ORSet** - Add and remove with re-add support

### Maps
- **LWWMap** - Key-value map with last-writer-wins semantics

### Sequences
- **RGA** - Replicated Growable Array for ordered lists/text

## Quick Start

```lean
import Convergent

open Convergent

-- Create replica identifiers
let r1 : ReplicaId := 1
let r2 : ReplicaId := 2

-- GCounter example
let counter := GCounter.empty
  |> fun s => GCounter.apply s (GCounter.increment r1)
  |> fun s => GCounter.apply s (GCounter.increment r2)
-- counter.value = 2

-- ORSet example
let tag1 := UniqueId.mk r1 0
let tag2 := UniqueId.mk r1 1
let set := ORSet.empty
  |> fun s => ORSet.apply s (ORSet.add "apple" tag1)
  |> fun s => ORSet.apply s (ORSet.add "banana" tag2)
-- set.contains "apple" = true

-- LWWRegister example
let ts1 := LamportTs.mk 1 r1
let ts2 := LamportTs.mk 2 r1
let reg := LWWRegister.empty
  |> fun s => LWWRegister.apply s (LWWRegister.set "first" ts1)
  |> fun s => LWWRegister.apply s (LWWRegister.set "second" ts2)
-- reg.get = some "second"
```

## Core Concepts

### ReplicaId
Each node in your distributed system needs a unique `ReplicaId`:
```lean
let myReplica : ReplicaId := 42
```

### Timestamps
For ordering operations:
```lean
-- Lamport timestamp (total order)
let ts := LamportTs.mk 1 myReplica

-- Vector clock (causal order)
let vc := VectorClock.empty.inc myReplica
```

### UniqueId
For tagging operations in OR-Set and RGA:
```lean
let gen := UniqueIdGen.init myReplica
let (id, gen') := gen.next
```

## Operation-based Semantics

1. Create operations locally
2. Apply to local state immediately
3. Broadcast operations to other replicas
4. Other replicas apply received operations

Operations are commutative for concurrent execution, ensuring all replicas converge to the same state regardless of operation order.

## Building

```bash
lake build    # Build library
lake test     # Run tests
```

## License

MIT
