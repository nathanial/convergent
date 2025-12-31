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

  ### Maps
  - `LWWMap` - Last-writer-wins map

  ### Sequences
  - `RGA` - Replicated Growable Array (for lists/text)

  ## Quick Start

  ```lean
  import Convergent

  open Convergent

  -- Create a grow-only counter
  let r1 : ReplicaId := 1
  let counter := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment r1)
  -- counter.value = 1

  -- Create an OR-Set
  let tag := UniqueId.mk r1 0
  let set := ORSet.empty
    |> fun s => ORSet.apply s (ORSet.add "item" tag)
  -- set.contains "item" = true
  ```
-/

-- Core abstractions
import Convergent.Core.ReplicaId
import Convergent.Core.Timestamp
import Convergent.Core.UniqueId
import Convergent.Core.CmRDT

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

-- Maps
import Convergent.Map.LWWMap

-- Sequences
import Convergent.Sequence.RGA

namespace Convergent
end Convergent
