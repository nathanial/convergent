/-
  Serialization Round-Trip Tests

  Verifies that encode/decode round-trips correctly for all CRDT types.
-/
import Convergent
import Convergent.Serialization
import Crucible

namespace ConvergentTests.SerializationTests

open Crucible
open Convergent
open Convergent.Serialization

/-! ## Helper for round-trip testing -/

def roundTripOk [BinarySerialize α] [BEq α] (val : α) : Bool :=
  match BinarySerialize.roundTrip val with
  | some decoded => decoded == val
  | none => false

testSuite "Serialization"

/-! ## Primitive Tests -/

test "Nat round-trip small" := do
  (roundTripOk (42 : Nat)) ≡ true

test "Nat round-trip zero" := do
  (roundTripOk (0 : Nat)) ≡ true

test "Nat round-trip large" := do
  (roundTripOk (123456789 : Nat)) ≡ true

test "Int round-trip positive" := do
  (roundTripOk (42 : Int)) ≡ true

test "Int round-trip negative" := do
  (roundTripOk (-42 : Int)) ≡ true

test "Bool round-trip" := do
  (roundTripOk true) ≡ true
  (roundTripOk false) ≡ true

test "String round-trip" := do
  (roundTripOk "hello world") ≡ true
  (roundTripOk "") ≡ true

/-! ## Core Type Tests -/

test "ReplicaId round-trip" := do
  (roundTripOk (ReplicaId.mk 42)) ≡ true

test "UniqueId round-trip" := do
  (roundTripOk (UniqueId.mk (ReplicaId.mk 1) 100)) ≡ true

test "LamportTs round-trip" := do
  (roundTripOk (LamportTs.new 50 (ReplicaId.mk 3))) ≡ true

test "VectorClock round-trip" := do
  let vc := VectorClock.empty |>.inc (ReplicaId.mk 1) |>.inc (ReplicaId.mk 2)
  match BinarySerialize.roundTrip vc with
  | some decoded =>
    let r1 := ReplicaId.mk 1
    let r2 := ReplicaId.mk 2
    (decoded.get r1 == vc.get r1 && decoded.get r2 == vc.get r2) ≡ true
  | none => (false) ≡ true

/-! ## Counter Tests -/

test "GCounter round-trip empty" := do
  let gc := GCounter.empty
  match BinarySerialize.roundTrip gc with
  | some decoded => (decoded.value) ≡ gc.value
  | none => (false) ≡ true

test "GCounter round-trip with data" := do
  let gc := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment (ReplicaId.mk 1))
    |> fun s => GCounter.apply s (GCounter.increment (ReplicaId.mk 2))
  match BinarySerialize.roundTrip gc with
  | some decoded => (decoded.value) ≡ gc.value
  | none => (false) ≡ true

test "GCounterOp round-trip" := do
  let op := GCounterOp.mk (ReplicaId.mk 5) 3
  match BinarySerialize.roundTrip op with
  | some decoded =>
    (decoded.replica == op.replica && decoded.amount == op.amount) ≡ true
  | none => (false) ≡ true

test "PNCounter round-trip" := do
  let pn := PNCounter.empty
    |> fun s => PNCounter.apply s (PNCounter.increment (ReplicaId.mk 1))
    |> fun s => PNCounter.apply s (PNCounter.decrement (ReplicaId.mk 2))
  match BinarySerialize.roundTrip pn with
  | some decoded => (decoded.value) ≡ pn.value
  | none => (false) ≡ true

/-! ## Register Tests -/

test "LWWRegister round-trip empty" := do
  let reg : LWWRegister Nat := LWWRegister.empty
  match BinarySerialize.roundTrip reg with
  | some decoded => (decoded.get.isNone) ≡ true
  | none => (false) ≡ true

test "LWWRegister round-trip with value" := do
  let reg := LWWRegister.empty
    |> fun r => LWWRegister.apply r (LWWRegister.set 42 (LamportTs.new 1 (ReplicaId.mk 1)))
  match BinarySerialize.roundTrip reg with
  | some decoded => (decoded.get) ≡ some 42
  | none => (false) ≡ true

test "MVRegister round-trip" := do
  let reg := MVRegister.empty
    |> fun r => MVRegister.apply r (MVRegister.set 42 VectorClock.empty)
  match BinarySerialize.roundTrip reg with
  | some decoded => (decoded.get) ≡ [42]
  | none => (false) ≡ true

/-! ## Set Tests -/

test "GSet round-trip empty" := do
  let gs : GSet Nat := GSet.empty
  match BinarySerialize.roundTrip gs with
  | some decoded => (decoded.size) ≡ 0
  | none => (false) ≡ true

test "GSet round-trip with elements" := do
  let gs := GSet.empty
    |> fun s => GSet.apply s (GSet.add 1)
    |> fun s => GSet.apply s (GSet.add 2)
    |> fun s => GSet.apply s (GSet.add 3)
  match BinarySerialize.roundTrip gs with
  | some decoded =>
    (decoded.contains 1 && decoded.contains 2 && decoded.contains 3) ≡ true
  | none => (false) ≡ true

test "TwoPSet round-trip" := do
  let tps := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.add 1)
    |> fun s => TwoPSet.apply s (TwoPSet.add 2)
    |> fun s => TwoPSet.apply s (TwoPSet.remove 1)
  match BinarySerialize.roundTrip tps with
  | some decoded =>
    (!decoded.contains 1 && decoded.contains 2) ≡ true
  | none => (false) ≡ true

test "ORSet round-trip" := do
  let tag1 := UniqueId.mk (ReplicaId.mk 1) 1
  let tag2 := UniqueId.mk (ReplicaId.mk 1) 2
  let os := ORSet.empty
    |> fun s => ORSet.apply s (ORSet.add 10 tag1)
    |> fun s => ORSet.apply s (ORSet.add 20 tag2)
  match BinarySerialize.roundTrip os with
  | some decoded =>
    (decoded.contains 10 && decoded.contains 20) ≡ true
  | none => (false) ≡ true

/-! ## Flag Tests -/

test "EWFlag round-trip disabled" := do
  let f := EWFlag.empty
  match BinarySerialize.roundTrip f with
  | some decoded => (decoded.value) ≡ f.value
  | none => (false) ≡ true

test "EWFlag round-trip enabled" := do
  let ts := LamportTs.new 1 (ReplicaId.mk 1)
  let f := EWFlag.empty |> fun f => EWFlag.apply f (EWFlag.enable ts)
  match BinarySerialize.roundTrip f with
  | some decoded => (decoded.value) ≡ f.value
  | none => (false) ≡ true

test "DWFlag round-trip" := do
  let ts := LamportTs.new 1 (ReplicaId.mk 1)
  let f := DWFlag.empty |> fun f => DWFlag.apply f (DWFlag.enable ts)
  match BinarySerialize.roundTrip f with
  | some decoded => (decoded.value) ≡ f.value
  | none => (false) ≡ true

/-! ## Map Tests -/

test "LWWMap round-trip" := do
  let ts := LamportTs.new 1 (ReplicaId.mk 1)
  let m := LWWMap.empty
    |> fun m => LWWMap.apply m (LWWMap.put "a" 1 ts)
    |> fun m => LWWMap.apply m (LWWMap.put "b" 2 ts)
  match BinarySerialize.roundTrip m with
  | some decoded =>
    (decoded.get "a" == some 1 && decoded.get "b" == some 2) ≡ true
  | none => (false) ≡ true

test "PNMap round-trip" := do
  let m := PNMap.empty
    |> fun m => PNMap.apply m (PNMap.increment "count" (ReplicaId.mk 1))
    |> fun m => PNMap.apply m (PNMap.increment "count" (ReplicaId.mk 1))
  match BinarySerialize.roundTrip m with
  | some decoded => (decoded.get "count") ≡ m.get "count"
  | none => (false) ≡ true

/-! ## Sequence Tests -/

test "RGA round-trip empty" := do
  let rga : RGA Char := RGA.empty
  match BinarySerialize.roundTrip rga with
  | some decoded => (decoded.toList) ≡ rga.toList
  | none => (false) ≡ true

test "RGA round-trip with elements" := do
  let id1 := UniqueId.mk (ReplicaId.mk 1) 1
  let id2 := UniqueId.mk (ReplicaId.mk 1) 2
  let rga := RGA.empty
    |> fun r => RGA.apply r (RGA.insert none 'H' id1)
    |> fun r => RGA.apply r (RGA.insert (some id1) 'i' id2)
  match BinarySerialize.roundTrip rga with
  | some decoded => (decoded.toList) ≡ rga.toList
  | none => (false) ≡ true

test "LSEQ round-trip empty" := do
  let lseq : LSEQ Char := LSEQ.empty
  match BinarySerialize.roundTrip lseq with
  | some decoded => (decoded.toList) ≡ lseq.toList
  | none => (false) ≡ true

test "LSEQ round-trip with elements" := do
  let replica := ReplicaId.mk 1
  let (_, lseq) := LSEQ.insertAt LSEQ.empty replica 0 'A'
  let (_, lseq) := LSEQ.insertAt lseq replica 1 'B'
  match BinarySerialize.roundTrip lseq with
  | some decoded => (decoded.toList) ≡ lseq.toList
  | none => (false) ≡ true

test "LSEQId round-trip" := do
  let id := LSEQId.single 10 (ReplicaId.mk 1)
  (roundTripOk id) ≡ true

test "Fugue round-trip empty" := do
  let fugue : Fugue Char := Fugue.empty
  match BinarySerialize.roundTrip fugue with
  | some decoded => (decoded.toList) ≡ fugue.toList
  | none => (false) ≡ true

test "Fugue round-trip with elements" := do
  let replica := ReplicaId.mk 1
  let (_, fugue) := Fugue.insertAt Fugue.empty replica 0 'A'
  let (_, fugue) := Fugue.insertAt fugue replica 1 'B'
  match BinarySerialize.roundTrip fugue with
  | some decoded => (decoded.toList) ≡ fugue.toList
  | none => (false) ≡ true

test "FugueId round-trip" := do
  let id := FugueId.mk (ReplicaId.mk 1) 42
  (roundTripOk id) ≡ true

/-! ## Graph Tests -/

test "TwoPGraph round-trip empty" := do
  let g : TwoPGraph String := TwoPGraph.empty
  match BinarySerialize.roundTrip g with
  | some decoded => (decoded.vertexCount) ≡ 0
  | none => (false) ≡ true

test "TwoPGraph round-trip with data" := do
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "A")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "B")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "A" "B")
  match BinarySerialize.roundTrip g with
  | some decoded =>
    (decoded.containsVertex "A" && decoded.containsVertex "B" && decoded.containsEdge "A" "B") ≡ true
  | none => (false) ≡ true

/-! ## Container Tests -/

test "List round-trip" := do
  (roundTripOk [1, 2, 3, 4, 5]) ≡ true
  (roundTripOk ([] : List Nat)) ≡ true

test "Option round-trip" := do
  (roundTripOk (some 42)) ≡ true
  (roundTripOk (none : Option Nat)) ≡ true

test "Pair round-trip" := do
  (roundTripOk (1, "hello")) ≡ true

test "Array round-trip" := do
  (roundTripOk #[1, 2, 3]) ≡ true

end ConvergentTests.SerializationTests
