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

-- LSEQ Tests

testSuite "LSEQ"

test "LSEQ empty is empty" := do
  let lseq : LSEQ String := LSEQ.empty
  (lseq.toList) ≡ ([] : List String)
  (lseq.length) ≡ 0

test "LSEQ insert at start" := do
  let r1 : ReplicaId := 1
  let (_, lseq) := LSEQ.insertAt (LSEQ.empty : LSEQ String) r1 0 "hello"
  (lseq.toList) ≡ ["hello"]
  (lseq.length) ≡ 1

test "LSEQ insert multiple elements" := do
  let r1 : ReplicaId := 1
  let (_, lseq1) := LSEQ.insertAt (LSEQ.empty : LSEQ String) r1 0 "first"
  let (_, lseq2) := LSEQ.insertAt lseq1 r1 1 "second"
  let (_, lseq3) := LSEQ.insertAt lseq2 r1 2 "third"
  (lseq3.toList) ≡ ["first", "second", "third"]
  (lseq3.length) ≡ 3

test "LSEQ insert in middle" := do
  let r1 : ReplicaId := 1
  let (_, lseq1) := LSEQ.insertAt (LSEQ.empty : LSEQ String) r1 0 "first"
  let (_, lseq2) := LSEQ.insertAt lseq1 r1 1 "third"
  let (_, lseq3) := LSEQ.insertAt lseq2 r1 1 "second"
  (lseq3.toList) ≡ ["first", "second", "third"]

test "LSEQ delete marks tombstone" := do
  let r1 : ReplicaId := 1
  let (op1, lseq1) := LSEQ.insertAt (LSEQ.empty : LSEQ String) r1 0 "first"
  let (_, lseq2) := LSEQ.insertAt lseq1 r1 1 "second"
  -- Get the ID of the first element and delete it
  match op1 with
  | .insert id _ =>
    let lseq3 := LSEQ.apply lseq2 (LSEQ.delete id)
    (lseq3.toList) ≡ ["second"]
    (lseq3.length) ≡ 1
  | _ => pure ()

test "LSEQ delete is idempotent" := do
  let r1 : ReplicaId := 1
  let (op, lseq1) := LSEQ.insertAt (LSEQ.empty : LSEQ String) r1 0 "hello"
  match op with
  | .insert id _ =>
    let lseq2 := LSEQ.apply lseq1 (LSEQ.delete id)
    let lseq3 := LSEQ.apply lseq2 (LSEQ.delete id)
    (lseq3.toList) ≡ ([] : List String)
  | _ => pure ()

test "LSEQ apply insert with explicit ID" := do
  let r1 : ReplicaId := 1
  let id := LSEQId.single 5 r1
  let lseq := LSEQ.apply (LSEQ.empty : LSEQ String) (LSEQ.insert id "hello")
  (lseq.toList) ≡ ["hello"]
  (lseq.containsId id) ≡ true

test "LSEQ duplicate insert ignored" := do
  let r1 : ReplicaId := 1
  let id := LSEQId.single 5 r1
  let lseq := LSEQ.empty
    |> fun s => LSEQ.apply s (LSEQ.insert id "hello")
    |> fun s => LSEQ.apply s (LSEQ.insert id "duplicate")
  (lseq.toList) ≡ ["hello"]
  (lseq.length) ≡ 1

test "LSEQ merge combines elements" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let id1 := LSEQId.single 3 r1
  let id2 := LSEQId.single 7 r2
  let lseq1 := LSEQ.apply (LSEQ.empty : LSEQ String) (LSEQ.insert id1 "from r1")
  let lseq2 := LSEQ.apply (LSEQ.empty : LSEQ String) (LSEQ.insert id2 "from r2")
  let merged := LSEQ.merge lseq1 lseq2
  (merged.length) ≡ 2
  -- id1 (pos 3) should come before id2 (pos 7)
  (merged.toList) ≡ ["from r1", "from r2"]

test "LSEQ merge tombstone wins" := do
  let r1 : ReplicaId := 1
  let id := LSEQId.single 5 r1
  let lseq1 := LSEQ.apply (LSEQ.empty : LSEQ String) (LSEQ.insert id "hello")
  let lseq2 := LSEQ.apply (LSEQ.empty : LSEQ String) (LSEQ.delete id)
  let merged := LSEQ.merge lseq1 lseq2
  (merged.toList) ≡ ([] : List String)
  (merged.containsId id) ≡ true  -- Tombstone still exists

test "LSEQ position ordering" := do
  let r1 : ReplicaId := 1
  let id1 := LSEQId.single 10 r1
  let id2 := LSEQId.single 5 r1
  let id3 := LSEQId.single 15 r1
  let lseq := LSEQ.empty
    |> fun s => LSEQ.apply s (LSEQ.insert id1 "mid")
    |> fun s => LSEQ.apply s (LSEQ.insert id2 "first")
    |> fun s => LSEQ.apply s (LSEQ.insert id3 "last")
  -- Elements should be ordered by position: 5, 10, 15
  (lseq.toList) ≡ ["first", "mid", "last"]

#generate_tests

end ConvergentTests.SequenceTests
