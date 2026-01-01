/-
  Convergent - Operation-based CRDTs for Lean 4

  A library implementing Conflict-free Replicated Data Types (CRDTs)
  using operation-based (CmRDT) semantics.

  CRDTs are data structures that can be replicated across multiple
  nodes and modified independently, with a mathematically guaranteed
  way to merge concurrent changes without conflicts.

  ## Available CRDTs

  ### Counters
  - `GCounter` - Grow-only counter
  - `PNCounter` - Positive-negative counter (supports decrement)

  ### Registers
  - `LWWRegister` - Last-writer-wins register
  - `MVRegister` - Multi-value register (preserves concurrent writes)

  ### Sets
  - `GSet` - Grow-only set
  - `TwoPSet` - Two-phase set (add/remove, no re-add)
  - `ORSet` - Observed-remove set (supports re-add)
  - `LWWElementSet` - Last-writer-wins element set (per-element timestamps)

  ### Maps
  - `LWWMap` - Last-writer-wins map
  - `ORMap` - Observed-remove map (add-wins, supports re-add)
  - `PNMap` - Map with PNCounter values (per-key increment/decrement)

  ### Sequences
  - `RGA` - Replicated Growable Array (for lists/text)
  - `LSEQ` - Adaptive sequence CRDT (position-based, for long documents)
  - `Fugue` - Text CRDT with maximal non-interleaving (tree-based)

  ### Flags
  - `EWFlag` - Enable-wins flag (concurrent enable + disable = enabled)
  - `DWFlag` - Disable-wins flag (concurrent enable + disable = disabled)

  ### Graphs
  - `TwoPGraph` - Two-phase graph (vertices and edges are two-phase sets)

  ## Quick Start

  ```lean
  import Convergent

  open Convergent

  -- Create a grow-only counter using the monadic interface
  let r1 : ReplicaId := 1
  let counter := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r1
  -- counter.value = 2

  -- Create an OR-Set
  let tag := UniqueId.mk r1 0
  let set := runCRDT ORSet.empty do
    ORSet.addM "item" tag
  -- set.contains "item" = true
  ```
-/

-- Core abstractions
import Convergent.Core.ReplicaId
import Convergent.Core.Timestamp
import Convergent.Core.UniqueId
import Convergent.Core.CmRDT
import Convergent.Core.Monad

-- Counters
import Convergent.Counter.GCounter
import Convergent.Counter.PNCounter

-- Registers
import Convergent.Register.LWWRegister
import Convergent.Register.MVRegister

-- Sets
import Convergent.Set.GSet
import Convergent.Set.TwoPSet
import Convergent.Set.ORSet
import Convergent.Set.LWWElementSet

-- Maps
import Convergent.Map.LWWMap
import Convergent.Map.ORMap
import Convergent.Map.PNMap

-- Sequences
import Convergent.Sequence.RGA
import Convergent.Sequence.LSEQ
import Convergent.Sequence.Fugue

-- Flags
import Convergent.Flag.EWFlag
import Convergent.Flag.DWFlag

-- Graphs
import Convergent.Graph.TwoPGraph

-- Serialization
import Convergent.Serialization

namespace Convergent
end Convergent
