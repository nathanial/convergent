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
  let gs := GSet.apply GSet.empty (GSet.add 42)
  (gs.contains 42) ≡ true

test "GSet add is idempotent" := do
  let gs := GSet.empty
    |> fun s => GSet.apply s (GSet.add 1)
    |> fun s => GSet.apply s (GSet.add 1)
    |> fun s => GSet.apply s (GSet.add 1)
  (gs.size) ≡ 1

test "GSet multiple elements" := do
  let gs := GSet.empty
    |> fun s => GSet.apply s (GSet.add 1)
    |> fun s => GSet.apply s (GSet.add 2)
    |> fun s => GSet.apply s (GSet.add 3)
  (gs.contains 1) ≡ true
  (gs.contains 2) ≡ true
  (gs.contains 3) ≡ true
  (gs.size) ≡ 3

testSuite "TwoPSet"

test "TwoPSet empty contains nothing" := do
  let tps : TwoPSet Nat := TwoPSet.empty
  (tps.contains 1) ≡ false

test "TwoPSet add makes present" := do
  let tps := TwoPSet.apply TwoPSet.empty (TwoPSet.add 42)
  (tps.contains 42) ≡ true

test "TwoPSet remove makes absent" := do
  let tps := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.add 42)
    |> fun s => TwoPSet.apply s (TwoPSet.remove 42)
  (tps.contains 42) ≡ false

test "TwoPSet cannot re-add" := do
  let tps := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.add 42)
    |> fun s => TwoPSet.apply s (TwoPSet.remove 42)
    |> fun s => TwoPSet.apply s (TwoPSet.add 42)
  (tps.contains 42) ≡ false

test "TwoPSet remove before add" := do
  let tps := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.remove 42)
    |> fun s => TwoPSet.apply s (TwoPSet.add 42)
  (tps.contains 42) ≡ false

testSuite "ORSet"

test "ORSet empty contains nothing" := do
  let os : ORSet Nat := ORSet.empty
  (os.contains 1) ≡ false

test "ORSet add makes present" := do
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 0
  let os := ORSet.apply ORSet.empty (ORSet.add 42 tag)
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
  let os'' := ORSet.apply os' (ORSet.add 42 tag2)
  (os''.contains 42) ≡ true

test "ORSet concurrent add wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tag1 := UniqueId.new r1 0
  let tag2 := UniqueId.new r2 0
  let os := ORSet.empty
    |> fun s => ORSet.apply s (ORSet.add 42 tag1)
  let removeOp := ORSet.remove os 42
  let os' := os
    |> fun s => ORSet.apply s (ORSet.add 42 tag2)
    |> fun s => ORSet.apply s removeOp
  (os'.contains 42) ≡ true

#generate_tests

end ConvergentTests.SetTests
