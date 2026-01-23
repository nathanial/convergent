import Convergent
import Crucible

namespace ConvergentTests.SetTests

open Crucible
open Convergent

testSuite "GSet"

test "GSet empty contains nothing" := do
  let gs : GSet Nat := GSet.empty
  (gs.contains 1) ≡ false

test "GSet add makes present" := do
  let gs := runCRDT GSet.empty do
    GSet.addM 42
  (gs.contains 42) ≡ true

test "GSet add is idempotent" := do
  let gs := runCRDT GSet.empty do
    GSet.addM 1
    GSet.addM 1
    GSet.addM 1
  (gs.size) ≡ 1

test "GSet multiple elements" := do
  let gs := runCRDT GSet.empty do
    GSet.addM 1
    GSet.addM 2
    GSet.addM 3
  (gs.contains 1) ≡ true
  (gs.contains 2) ≡ true
  (gs.contains 3) ≡ true
  (gs.size) ≡ 3

testSuite "TwoPSet"

test "TwoPSet empty contains nothing" := do
  let tps : TwoPSet Nat := TwoPSet.empty
  (tps.contains 1) ≡ false

test "TwoPSet add makes present" := do
  let tps := runCRDT TwoPSet.empty do
    TwoPSet.addM 42
  (tps.contains 42) ≡ true

test "TwoPSet remove makes absent" := do
  let tps := runCRDT TwoPSet.empty do
    TwoPSet.addM 42
    TwoPSet.removeM 42
  (tps.contains 42) ≡ false

test "TwoPSet cannot re-add" := do
  let tps := runCRDT TwoPSet.empty do
    TwoPSet.addM 42
    TwoPSet.removeM 42
    TwoPSet.addM 42
  (tps.contains 42) ≡ false

test "TwoPSet remove before add" := do
  let tps := runCRDT TwoPSet.empty do
    TwoPSet.removeM 42
    TwoPSet.addM 42
  (tps.contains 42) ≡ false

testSuite "ORSet"

test "ORSet empty contains nothing" := do
  let os : ORSet Nat := ORSet.empty
  (os.contains 1) ≡ false

test "ORSet add makes present" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 0
  let os := runCRDT ORSet.empty do
    ORSet.addM 42 tag
  (os.contains 42) ≡ true

test "ORSet remove removes" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 0
  let os := ORSet.apply ORSet.empty (ORSet.add 42 tag)
  let removeOp := ORSet.remove os 42
  let os' := ORSet.apply os removeOp
  (os'.contains 42) ≡ false

test "ORSet can re-add" := do
  let r1 : ReplicaId := 1
  let tag1 := UniqueId.new r1 0
  let tag2 := UniqueId.new r1 1
  let os := ORSet.apply ORSet.empty (ORSet.add 42 tag1)
  let removeOp := ORSet.remove os 42
  let os' := ORSet.apply os removeOp
  let os'' := runCRDT os' do
    ORSet.addM 42 tag2
  (os''.contains 42) ≡ true

test "ORSet concurrent add wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tag1 := UniqueId.new r1 0
  let tag2 := UniqueId.new r2 0
  let os := runCRDT ORSet.empty do
    ORSet.addM 42 tag1
  let removeOp := ORSet.remove os 42
  let observedTags := match removeOp with
    | .remove _ tags => tags
    | _ => []
  let os' := runCRDT os do
    ORSet.addM 42 tag2
    ORSet.removeWithTagsM 42 observedTags
  (os'.contains 42) ≡ true

testSuite "LWWElementSet"

test "LWWElementSet empty contains nothing" := do
  let set : LWWElementSet Nat := LWWElementSet.empty
  (set.contains 1) ≡ false

test "LWWElementSet add makes present" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 42 ts
  (set.contains 42) ≡ true

test "LWWElementSet remove makes absent" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 42 ts1
    LWWElementSet.removeM 42 ts2
  (set.contains 42) ≡ false

test "LWWElementSet later timestamp wins (add after remove)" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  -- Remove at ts1, then add at ts2 (later) - add wins
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.removeM 42 ts1
    LWWElementSet.addM 42 ts2
  (set.contains 42) ≡ true

test "LWWElementSet later timestamp wins (remove after add)" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  -- Add at ts1, then remove at ts2 (later) - remove wins
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 42 ts1
    LWWElementSet.removeM 42 ts2
  (set.contains 42) ≡ false

test "LWWElementSet equal timestamps add-wins" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  -- Remove at ts, then add at same ts - add wins (bias)
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.removeM 42 ts
    LWWElementSet.addM 42 ts
  (set.contains 42) ≡ true

test "LWWElementSet can re-add after remove" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let ts3 := LamportTs.new 3 r1
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 42 ts1
    LWWElementSet.removeM 42 ts2
    LWWElementSet.addM 42 ts3
  (set.contains 42) ≡ true

test "LWWElementSet multiple elements" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let ts3 := LamportTs.new 3 r1
  let set := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 1 ts1
    LWWElementSet.addM 2 ts2
    LWWElementSet.addM 3 ts3
  (set.contains 1) ≡ true
  (set.contains 2) ≡ true
  (set.contains 3) ≡ true
  (set.size) ≡ 3

test "LWWElementSet merge combines entries" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 1 r2
  let setA := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 1 ts1
  let setB := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 2 ts2
  let merged := LWWElementSet.merge setA setB
  (merged.contains 1) ≡ true
  (merged.contains 2) ≡ true

test "LWWElementSet merge takes higher timestamp" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r2
  -- setA has element added at ts1
  -- setB has element removed at ts2 (later)
  let setA := runCRDT LWWElementSet.empty do
    LWWElementSet.addM 42 ts1
  let setB := runCRDT LWWElementSet.empty do
    LWWElementSet.removeM 42 ts2
  let merged := LWWElementSet.merge setA setB
  (merged.contains 42) ≡ false  -- ts2 > ts1, so remove wins

end ConvergentTests.SetTests
