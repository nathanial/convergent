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

test "RGA insert after preserves relative order even if ids conflict" := do
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 2
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

test "LSEQ allocateBetween stays between equal-pos bounds" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let r3 : ReplicaId := 3
  let lower : LSEQId := { levels := [{ pos := 5, site := r1 }] }
  let upper : LSEQId := { levels := [{ pos := 5, site := r2 }] }
  let newId := LSEQ.allocateBetween r3 (some lower) (some upper)
  (compare lower newId == .lt) ≡ true
  (compare newId upper == .lt) ≡ true
  (newId.levels.head?.map (·.site)) ≡ some r1

-- Fugue Tests

testSuite "Fugue"

test "Fugue empty is empty" := do
  let f : Fugue String := Fugue.empty
  (f.toList) ≡ ([] : List String)
  (f.length) ≡ 0

test "Fugue insert at start" := do
  let r1 : ReplicaId := 1
  let (_, f) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "hello"
  (f.toList) ≡ ["hello"]
  (f.length) ≡ 1

test "Fugue insert multiple elements" := do
  let r1 : ReplicaId := 1
  let (_, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "first"
  let (_, f2) := Fugue.insertAt f1 r1 1 "second"
  let (_, f3) := Fugue.insertAt f2 r1 2 "third"
  (f3.toList) ≡ ["first", "second", "third"]
  (f3.length) ≡ 3

test "Fugue insert in middle" := do
  let r1 : ReplicaId := 1
  let (_, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "first"
  let (_, f2) := Fugue.insertAt f1 r1 1 "third"
  let (_, f3) := Fugue.insertAt f2 r1 1 "second"
  (f3.toList) ≡ ["first", "second", "third"]

test "Fugue delete marks tombstone" := do
  let r1 : ReplicaId := 1
  let (op1, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "first"
  let (_, f2) := Fugue.insertAt f1 r1 1 "second"
  match op1 with
  | .insert node =>
    let f3 := Fugue.apply f2 (Fugue.delete node.id)
    (f3.toList) ≡ ["second"]
    (f3.length) ≡ 1
  | _ => pure ()

test "Fugue delete is idempotent" := do
  let r1 : ReplicaId := 1
  let (op, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "hello"
  match op with
  | .insert node =>
    let f2 := Fugue.apply f1 (Fugue.delete node.id)
    let f3 := Fugue.apply f2 (Fugue.delete node.id)
    (f3.toList) ≡ ([] : List String)
  | _ => pure ()

test "Fugue duplicate insert ignored" := do
  let r1 : ReplicaId := 1
  let id := FugueId.mk r1 1
  let node1 : FugueNode String := {
    id := id
    value := some "hello"
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let node2 : FugueNode String := {
    id := id
    value := some "duplicate"
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f := Fugue.empty
    |> fun s => Fugue.apply s (Fugue.insert node1)
    |> fun s => Fugue.apply s (Fugue.insert node2)
  (f.toList) ≡ ["hello"]
  (f.length) ≡ 1

test "Fugue merge combines elements" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let (_, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "from r1"
  let (_, f2) := Fugue.insertAt (Fugue.empty : Fugue String) r2 0 "from r2"
  let merged := Fugue.merge f1 f2
  (merged.length) ≡ 2

test "Fugue merge tombstone wins" := do
  let r1 : ReplicaId := 1
  let id := FugueId.mk r1 1
  let node : FugueNode String := {
    id := id
    value := some "hello"
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f1 := Fugue.apply (Fugue.empty : Fugue String) (Fugue.insert node)
  let f2 := Fugue.apply (Fugue.empty : Fugue String) (Fugue.delete id)
  let merged := Fugue.merge f1 f2
  (merged.toList) ≡ ([] : List String)
  (merged.containsId id) ≡ true  -- Tombstone still exists

test "Fugue concurrent inserts from different replicas" := do
  -- Two replicas insert at position 0 concurrently
  -- The result should be deterministic (by replica ID ordering)
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let (op1, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "from r1"
  let (op2, f2) := Fugue.insertAt (Fugue.empty : Fugue String) r2 0 "from r2"
  -- Apply ops from both replicas to each other
  let merged1 := Fugue.apply f1 op2
  let merged2 := Fugue.apply f2 op1
  -- Both should converge to same state
  (merged1.length) ≡ 2
  (merged2.length) ≡ 2
  -- Order should be deterministic
  (merged1.toList) ≡ (merged2.toList)

test "Fugue contains ID after insert" := do
  let r1 : ReplicaId := 1
  let id := FugueId.mk r1 1
  let node : FugueNode String := {
    id := id
    value := some "hello"
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f := Fugue.apply Fugue.empty (Fugue.insert node)
  (f.containsId id) ≡ true

test "Fugue delete makes element invisible but keeps ID" := do
  let r1 : ReplicaId := 1
  let id := FugueId.mk r1 1
  let node : FugueNode String := {
    id := id
    value := some "hello"
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f := Fugue.apply Fugue.empty (Fugue.insert node)
  let f' := Fugue.apply f (Fugue.delete id)
  (f'.containsId id) ≡ true
  (f'.length) ≡ 0

test "Fugue handles parent cycles without looping" := do
  let r1 : ReplicaId := 1
  let id1 := FugueId.mk r1 1
  let id2 := FugueId.mk r1 2
  let node1 : FugueNode String := {
    id := id1
    value := some "a"
    parent := some id2
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let node2 : FugueNode String := {
    id := id2
    value := some "b"
    parent := some id1
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f := Fugue.empty
    |> fun s => Fugue.apply s (Fugue.insert node1)
    |> fun s => Fugue.apply s (Fugue.insert node2)
  let values := f.toList
  (decide (values.length <= 2)) ≡ true
  (Fugue.isAncestor f id1 id2) ≡ true

test "Fugue ignores unreachable cycles in toList" := do
  let r1 : ReplicaId := 1
  let id1 := FugueId.mk r1 1
  let id2 := FugueId.mk r1 2
  let node1 : FugueNode String := {
    id := id1
    value := some "a"
    parent := some id2
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let node2 : FugueNode String := {
    id := id2
    value := some "b"
    parent := some id1
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f := Fugue.empty
    |> fun s => Fugue.apply s (Fugue.insert node1)
    |> fun s => Fugue.apply s (Fugue.insert node2)
  (f.toList) ≡ ([] : List String)

test "Fugue ignores unreachable cycle but keeps reachable nodes" := do
  let r1 : ReplicaId := 1
  let rootId := FugueId.mk r1 10
  let root : FugueNode String := {
    id := rootId
    value := some "root"
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let cycleId1 := FugueId.mk r1 1
  let cycleId2 := FugueId.mk r1 2
  let cycleNode1 : FugueNode String := {
    id := cycleId1
    value := some "cycle-a"
    parent := some cycleId2
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let cycleNode2 : FugueNode String := {
    id := cycleId2
    value := some "cycle-b"
    parent := some cycleId1
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let f := Fugue.empty
    |> fun s => Fugue.apply s (Fugue.insert root)
    |> fun s => Fugue.apply s (Fugue.insert cycleNode1)
    |> fun s => Fugue.apply s (Fugue.insert cycleNode2)
  (f.toList) ≡ ["root"]

end ConvergentTests.SequenceTests
