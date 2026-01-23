import Convergent
import Crucible

namespace ConvergentTests.MapTests

open Crucible
open Convergent

testSuite "LWWMap"

test "LWWMap empty returns none" := do
  let m : LWWMap String Nat := LWWMap.empty
  (m.get "key") ≡ (none : Option Nat)

test "LWWMap put adds value" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  let m := LWWMap.apply LWWMap.empty (LWWMap.put "key" 42 ts)
  (m.get "key") ≡ some 42

test "LWWMap later put wins" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "key" 1 ts1)
    |> fun s => LWWMap.apply s (LWWMap.put "key" 2 ts2)
  (m.get "key") ≡ some 2

test "LWWMap delete removes key" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "key" 42 ts1)
    |> fun s => LWWMap.apply s (LWWMap.delete "key" ts2)
  (m.get "key") ≡ (none : Option Nat)
  (m.contains "key") ≡ false

test "LWWMap put after delete" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let ts3 := LamportTs.new 3 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "key" 42 ts1)
    |> fun s => LWWMap.apply s (LWWMap.delete "key" ts2)
    |> fun s => LWWMap.apply s (LWWMap.put "key" 100 ts3)
  (m.get "key") ≡ some 100

test "LWWMap multiple keys" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "a" 1 ts)
    |> fun s => LWWMap.apply s (LWWMap.put "b" 2 ts)
    |> fun s => LWWMap.apply s (LWWMap.put "c" 3 ts)
  (m.size) ≡ 3
  (m.get "a") ≡ some 1
  (m.get "b") ≡ some 2
  (m.get "c") ≡ some 3

-- ORMap tests (simple values)
testSuite "ORMap"

test "ORMap empty contains nothing" := do
  let m : ORMap String Nat Unit := ORMap.empty
  (m.contains "key") ≡ false
  (m.get "key") ≡ []

test "ORMap put adds value" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 1
  let m : ORMap String Nat Unit := ORMap.apply ORMap.empty (ORMap.put "key" 42 tag)
  (m.contains "key") ≡ true
  (m.get "key") ≡ [42]

test "ORMap delete removes key" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 1
  let m : ORMap String Nat Unit := ORMap.empty
    |> fun s => ORMap.apply s (ORMap.put "key" 42 tag)
  let deleteOp := ORMap.delete m "key"
  let m' := ORMap.apply m deleteOp
  (m'.contains "key") ≡ false
  (m'.get "key") ≡ []

test "ORMap can re-add after delete" := do
  let r1 : ReplicaId := 1
  let tag1 := UniqueId.new r1 1
  let tag2 := UniqueId.new r1 2
  let m : ORMap String Nat Unit := ORMap.empty
    |> fun s => ORMap.apply s (ORMap.put "key" 42 tag1)
  let deleteOp := ORMap.delete m "key"
  let m' := ORMap.apply m deleteOp
    |> fun s => ORMap.apply s (ORMap.put "key" 100 tag2)
  (m'.contains "key") ≡ true
  (m'.get "key") ≡ [100]

test "ORMap concurrent adds preserved" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tag1 := UniqueId.new r1 1
  let tag2 := UniqueId.new r2 1
  let m : ORMap String Nat Unit := ORMap.empty
    |> fun s => ORMap.apply s (ORMap.put "key" 42 tag1)
    |> fun s => ORMap.apply s (ORMap.put "key" 100 tag2)
  (m.contains "key") ≡ true
  (m.get "key").length ≡ 2

-- Nested CRDT tests (ORMap with PNCounter values)
testSuite "ORMap Nested CRDTs"

test "ORMap with nested PNCounter" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 1
  -- Create map with counter value
  let m : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (.put "visitors" PNCounter.empty tag)
  (m.contains "visitors") ≡ true
  -- Initial counter value is 0
  (m.getOne "visitors" |>.map (·.value)) ≡ some 0

test "ORMap update applies nested op" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 1
  -- Create map and increment counter
  let m : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (.put "visitors" PNCounter.empty tag)
    |> fun s => ORMap.apply s (.update "visitors" tag (.increment r1))
    |> fun s => ORMap.apply s (.update "visitors" tag (.increment r1))
  (m.getOne "visitors" |>.map (·.value)) ≡ some 2

test "ORMap update decrement works" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 1
  let m : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (.put "score" PNCounter.empty tag)
    |> fun s => ORMap.apply s (.update "score" tag (.increment r1))
    |> fun s => ORMap.apply s (.update "score" tag (.increment r1))
    |> fun s => ORMap.apply s (.update "score" tag (.decrement r1))
  (m.getOne "score" |>.map (·.value)) ≡ some 1

test "ORMap merge recursively merges nested counters" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tag := UniqueId.new r1 1  -- Same tag on both replicas
  -- Replica 1: counter with value 2
  let m1 : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (.put "count" PNCounter.empty tag)
    |> fun s => ORMap.apply s (.update "count" tag (.increment r1))
    |> fun s => ORMap.apply s (.update "count" tag (.increment r1))
  -- Replica 2: counter with value 3
  let m2 : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (.put "count" PNCounter.empty tag)
    |> fun s => ORMap.apply s (.update "count" tag (.increment r2))
    |> fun s => ORMap.apply s (.update "count" tag (.increment r2))
    |> fun s => ORMap.apply s (.update "count" tag (.increment r2))
  -- Merge: should get max per replica = 2 + 3 = 5
  let merged := ORMap.merge m1 m2
  (merged.getOne "count" |>.map (·.value)) ≡ some 5

test "ORMap multiple keys with nested counters" := do
  let r1 : ReplicaId := 1
  let tag1 := UniqueId.new r1 1
  let tag2 := UniqueId.new r1 2
  let m : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (.put "likes" PNCounter.empty tag1)
    |> fun s => ORMap.apply s (.put "views" PNCounter.empty tag2)
    |> fun s => ORMap.apply s (.update "likes" tag1 (.increment r1))
    |> fun s => ORMap.apply s (.update "views" tag2 (.increment r1))
    |> fun s => ORMap.apply s (.update "views" tag2 (.increment r1))
  (m.getOne "likes" |>.map (·.value)) ≡ some 1
  (m.getOne "views" |>.map (·.value)) ≡ some 2

-- Deeply nested: ORMap of ORMap of PNCounter (3 levels)
-- Type: user -> (metric -> counter)
abbrev InnerMap := ORMap String PNCounter PNCounterOp
abbrev OuterMap := ORMap String InnerMap (ORMapOp String PNCounter PNCounterOp)

test "ORMap deeply nested - map of maps of counters" := do
  let r1 : ReplicaId := 1
  let outerTag := UniqueId.new r1 1
  let innerTag := UniqueId.new r1 2
  -- Create outer map with an inner map for "alice"
  let innerMap : InnerMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "score" PNCounter.empty innerTag)
  let m : OuterMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "alice" innerMap outerTag)
  -- Verify structure
  (m.contains "alice") ≡ true
  match m.getOne "alice" with
  | some inner => (inner.getOne "score" |>.map (·.value)) ≡ some 0
  | none => pure ()

test "ORMap deeply nested - update inner map" := do
  let r1 : ReplicaId := 1
  let outerTag := UniqueId.new r1 1
  let innerTag := UniqueId.new r1 2
  -- Create structure
  let innerMap : InnerMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "score" PNCounter.empty innerTag)
  let m : OuterMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "alice" innerMap outerTag)
    -- Update the inner map: increment alice's score counter
    |> fun s => ORMap.apply s (.update "alice" outerTag
        (.update "score" innerTag (.increment r1)))
    |> fun s => ORMap.apply s (.update "alice" outerTag
        (.update "score" innerTag (.increment r1)))
  -- Verify alice's score is 2
  match m.getOne "alice" with
  | some inner => (inner.getOne "score" |>.map (·.value)) ≡ some 2
  | none => pure ()

test "ORMap deeply nested - multiple users" := do
  let r1 : ReplicaId := 1
  let aliceOuterTag := UniqueId.new r1 1
  let bobOuterTag := UniqueId.new r1 2
  let aliceScoreTag := UniqueId.new r1 3
  let bobScoreTag := UniqueId.new r1 4
  -- Create maps for alice and bob
  let aliceMap : InnerMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "score" PNCounter.empty aliceScoreTag)
  let bobMap : InnerMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "score" PNCounter.empty bobScoreTag)
  let m : OuterMap := ORMap.empty
    |> fun s => ORMap.apply s (.put "alice" aliceMap aliceOuterTag)
    |> fun s => ORMap.apply s (.put "bob" bobMap bobOuterTag)
    -- Alice scores 3 points
    |> fun s => ORMap.apply s (.update "alice" aliceOuterTag
        (.update "score" aliceScoreTag (.increment r1)))
    |> fun s => ORMap.apply s (.update "alice" aliceOuterTag
        (.update "score" aliceScoreTag (.increment r1)))
    |> fun s => ORMap.apply s (.update "alice" aliceOuterTag
        (.update "score" aliceScoreTag (.increment r1)))
    -- Bob scores 1 point
    |> fun s => ORMap.apply s (.update "bob" bobOuterTag
        (.update "score" bobScoreTag (.increment r1)))
  -- Verify
  match m.getOne "alice", m.getOne "bob" with
  | some alice, some bob =>
    (alice.getOne "score" |>.map (·.value)) ≡ some 3
    (bob.getOne "score" |>.map (·.value)) ≡ some 1
  | _, _ => pure ()

testSuite "PNMap"

test "PNMap empty returns 0" := do
  let m : PNMap String := PNMap.empty
  (m.get "key") ≡ 0

test "PNMap increment increases by 1" := do
  let r1 : ReplicaId := 1
  let m := PNMap.apply PNMap.empty (PNMap.increment "key" r1)
  (m.get "key") ≡ 1

test "PNMap decrement decreases by 1" := do
  let r1 : ReplicaId := 1
  let m := PNMap.empty
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
    |> fun s => PNMap.apply s (PNMap.decrement "key" r1)
  (m.get "key") ≡ 1

test "PNMap multiple increments" := do
  let r1 : ReplicaId := 1
  let m := PNMap.empty
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
  (m.get "key") ≡ 3

test "PNMap multiple keys" := do
  let r1 : ReplicaId := 1
  let m := PNMap.empty
    |> fun s => PNMap.apply s (PNMap.increment "a" r1)
    |> fun s => PNMap.apply s (PNMap.increment "b" r1)
    |> fun s => PNMap.apply s (PNMap.increment "b" r1)
    |> fun s => PNMap.apply s (PNMap.increment "c" r1)
    |> fun s => PNMap.apply s (PNMap.increment "c" r1)
    |> fun s => PNMap.apply s (PNMap.increment "c" r1)
  (m.get "a") ≡ 1
  (m.get "b") ≡ 2
  (m.get "c") ≡ 3

test "PNMap value can go negative" := do
  let r1 : ReplicaId := 1
  let m := PNMap.apply PNMap.empty (PNMap.decrement "key" r1)
  (m.get "key") ≡ -1

test "PNMap multiple replicas" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let m := PNMap.empty
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
    |> fun s => PNMap.apply s (PNMap.increment "key" r2)
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
  (m.get "key") ≡ 3

test "PNMap merge combines counters" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Map A: key has value 2 from r1
  let mA := PNMap.empty
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
    |> fun s => PNMap.apply s (PNMap.increment "key" r1)
  -- Map B: key has value 3 from r2
  let mB := PNMap.empty
    |> fun s => PNMap.apply s (PNMap.increment "key" r2)
    |> fun s => PNMap.apply s (PNMap.increment "key" r2)
    |> fun s => PNMap.apply s (PNMap.increment "key" r2)
  -- Merge should get 2 + 3 = 5
  let merged := PNMap.merge mA mB
  (merged.get "key") ≡ 5

test "PNMap merge different keys" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let mA := PNMap.apply PNMap.empty (PNMap.increment "a" r1)
  let mB := PNMap.apply PNMap.empty (PNMap.increment "b" r2)
  let merged := PNMap.merge mA mB
  (merged.get "a") ≡ 1
  (merged.get "b") ≡ 1

end ConvergentTests.MapTests
