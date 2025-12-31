import Convergent
import Crucible

namespace ConvergentTests.SequenceTests

open Crucible
open Convergent

testSuite "RGA"

test "RGA empty is empty" := do
  let rga : RGA String := RGA.empty
  (rga.toList) ≡ ([] : List String)
  (rga.length) ≡ 0

test "RGA insert at start" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let rga := RGA.apply RGA.empty (RGA.insert none "hello" id1)
  (rga.toList) ≡ ["hello"]

test "RGA insert multiple at start" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let id2 := UniqueId.new r1 1
  let id3 := UniqueId.new r1 2
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "c" id3)
    |> fun s => RGA.apply s (RGA.insert none "b" id2)
    |> fun s => RGA.apply s (RGA.insert none "a" id1)
  (rga.length) ≡ 3

test "RGA insert after element" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let id2 := UniqueId.new r1 1
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "first" id1)
    |> fun s => RGA.apply s (RGA.insert (some id1) "second" id2)
  (rga.toList) ≡ ["first", "second"]

test "RGA delete marks tombstone" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let id2 := UniqueId.new r1 1
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "first" id1)
    |> fun s => RGA.apply s (RGA.insert (some id1) "second" id2)
    |> fun s => RGA.apply s (RGA.delete id1)
  (rga.toList) ≡ ["second"]
  (rga.length) ≡ 1

test "RGA delete is idempotent" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "hello" id1)
    |> fun s => RGA.apply s (RGA.delete id1)
    |> fun s => RGA.apply s (RGA.delete id1)
  (rga.toList) ≡ ([] : List String)

test "RGA duplicate insert ignored" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "hello" id1)
    |> fun s => RGA.apply s (RGA.insert none "duplicate" id1)
  (rga.toList) ≡ ["hello"]
  (rga.length) ≡ 1

test "RGA concurrent inserts ordered" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let id1 := UniqueId.new r1 0
  let id2 := UniqueId.new r2 0
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "from r1" id1)
    |> fun s => RGA.apply s (RGA.insert none "from r2" id2)
  (rga.length) ≡ 2

#generate_tests

end ConvergentTests.SequenceTests
