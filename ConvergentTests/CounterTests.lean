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

testSuite "BoundedCounter"

test "BoundedCounter empty has value 0" := do
  let bc := BoundedCounter.empty 0 10
  (bc.value) ≡ 0

test "BoundedCounter increment increases" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty 0 10
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
  (bc.value) ≡ 1

test "BoundedCounter decrement decreases" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty 0 10
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.decrement r1)
  (bc.value) ≡ 1

test "BoundedCounter increment at max clamps value" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty 0 3
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)  -- exceeds max
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)  -- exceeds max
  -- Visible value clamped to max
  (bc.value) ≡ 3
  -- But raw value reflects actual operations
  (bc.rawValue) ≡ 5

test "BoundedCounter decrement at min clamps value" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty 0 10
    |> fun s => BoundedCounter.apply s (BoundedCounter.decrement r1)  -- below min
    |> fun s => BoundedCounter.apply s (BoundedCounter.decrement r1)  -- below min
  -- Visible value clamped to min
  (bc.value) ≡ 0
  -- But raw value reflects actual operations
  (bc.rawValue) ≡ -2

test "BoundedCounter value stays within bounds" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty 0 5
  -- Increment many times
  let bc := (List.range 20).foldl (fun s _ => BoundedCounter.apply s (BoundedCounter.increment r1)) bc
  (bc.value) ≡ 5
  (bc.atMax) ≡ true

test "BoundedCounter negative bounds" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty (-5) 5
    |> fun s => BoundedCounter.apply s (BoundedCounter.decrement r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.decrement r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.decrement r1)
  (bc.value) ≡ -3

test "BoundedCounter respects negative min" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty (-2) 10
  -- Decrement past min
  let bc := (List.range 10).foldl (fun s _ => BoundedCounter.apply s (BoundedCounter.decrement r1)) bc
  (bc.value) ≡ -2
  (bc.atMin) ≡ true

test "BoundedCounter merge respects bounds" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Both replicas increment towards max
  let bc1 := BoundedCounter.empty 0 5
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
  let bc2 := BoundedCounter.empty 0 5
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r2)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r2)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r2)
  -- After merge, raw value would be 6, but clamped to 5
  let merged := BoundedCounter.merge bc1 bc2
  (merged.value) ≡ 5

test "BoundedCounter can go from max to below" := do
  let r1 : ReplicaId := 1
  let bc := BoundedCounter.empty 0 3
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
    |> fun s => BoundedCounter.apply s (BoundedCounter.increment r1)
  (bc.value) ≡ 3
  (bc.atMax) ≡ true
  let bc := BoundedCounter.apply bc (BoundedCounter.decrement r1)
  (bc.value) ≡ 2
  (bc.atMax) ≡ false

#generate_tests

end ConvergentTests.CounterTests
