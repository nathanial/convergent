import Convergent
import Crucible

namespace ConvergentTests.CounterTests

open Crucible
open Convergent

testSuite "GCounter"

test "GCounter empty has value 0" := do
  (GCounter.empty.value) ≡ 0

test "GCounter single increment" := do
  let r1 : ReplicaId := 1
  let gc := GCounter.apply GCounter.empty (GCounter.increment r1)
  (gc.value) ≡ 1

test "GCounter multiple increments same replica" := do
  let r1 : ReplicaId := 1
  let gc := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment r1)
    |> fun s => GCounter.apply s (GCounter.increment r1)
    |> fun s => GCounter.apply s (GCounter.increment r1)
  (gc.value) ≡ 3

test "GCounter increments different replicas" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let gc := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment r1)
    |> fun s => GCounter.apply s (GCounter.increment r2)
    |> fun s => GCounter.apply s (GCounter.increment r1)
  (gc.value) ≡ 3
  (gc.getCount r1) ≡ 2
  (gc.getCount r2) ≡ 1

test "GCounter merge takes max" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let gcA := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment r1)
    |> fun s => GCounter.apply s (GCounter.increment r1)
  let gcB := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment r1)
    |> fun s => GCounter.apply s (GCounter.increment r2)
  let merged := GCounter.merge gcA gcB
  (merged.getCount r1) ≡ 2
  (merged.getCount r2) ≡ 1

testSuite "PNCounter"

test "PNCounter empty has value 0" := do
  (PNCounter.empty.value) ≡ 0

test "PNCounter increment increases" := do
  let r1 : ReplicaId := 1
  let pn := PNCounter.apply PNCounter.empty (PNCounter.increment r1)
  (pn.value) ≡ 1

test "PNCounter decrement decreases" := do
  let r1 : ReplicaId := 1
  let pn := PNCounter.empty
    |> fun s => PNCounter.apply s (PNCounter.increment r1)
    |> fun s => PNCounter.apply s (PNCounter.increment r1)
    |> fun s => PNCounter.apply s (PNCounter.decrement r1)
  (pn.value) ≡ 1

test "PNCounter can go negative" := do
  let r1 : ReplicaId := 1
  let pn := PNCounter.apply PNCounter.empty (PNCounter.decrement r1)
  (pn.value) ≡ -1

test "PNCounter concurrent ops" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let pn := PNCounter.empty
    |> fun s => PNCounter.apply s (PNCounter.increment r1)
    |> fun s => PNCounter.apply s (PNCounter.decrement r2)
    |> fun s => PNCounter.apply s (PNCounter.increment r1)
  (pn.value) ≡ 1

#generate_tests

end ConvergentTests.CounterTests
