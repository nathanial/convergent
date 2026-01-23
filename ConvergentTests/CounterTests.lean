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
  let gc := runCRDT GCounter.empty do
    GCounter.incM r1
  (gc.value) ≡ 1

test "GCounter multiple increments same replica" := do
  let r1 : ReplicaId := 1
  let gc := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r1
    GCounter.incM r1
  (gc.value) ≡ 3

test "GCounter increments different replicas" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let gc := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r2
    GCounter.incM r1
  (gc.value) ≡ 3
  (gc.getCount r1) ≡ 2
  (gc.getCount r2) ≡ 1

test "GCounter merge takes max" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let gcA := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r1
  let gcB := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r2
  let merged := GCounter.merge gcA gcB
  (merged.getCount r1) ≡ 2
  (merged.getCount r2) ≡ 1

testSuite "PNCounter"

test "PNCounter empty has value 0" := do
  (PNCounter.empty.value) ≡ 0

test "PNCounter increment increases" := do
  let r1 : ReplicaId := 1
  let pn := runCRDT PNCounter.empty do
    PNCounter.incM r1
  (pn.value) ≡ 1

test "PNCounter decrement decreases" := do
  let r1 : ReplicaId := 1
  let pn := runCRDT PNCounter.empty do
    PNCounter.incM r1
    PNCounter.incM r1
    PNCounter.decM r1
  (pn.value) ≡ 1

test "PNCounter can go negative" := do
  let r1 : ReplicaId := 1
  let pn := runCRDT PNCounter.empty do
    PNCounter.decM r1
  (pn.value) ≡ -1

test "PNCounter concurrent ops" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let pn := runCRDT PNCounter.empty do
    PNCounter.incM r1
    PNCounter.decM r2
    PNCounter.incM r1
  (pn.value) ≡ 1

end ConvergentTests.CounterTests
