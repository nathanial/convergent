# Convergent Examples

Each snippet is a small, focused example. You can paste these into a
Lean file in the `data/convergent` project and adapt as needed.

## Counters

```lean
import Convergent

open Convergent

def gcExample : Nat :=
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let gc := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r2
    GCounter.incByM r1 3
  gc.value
-- expected: 5
```

```lean
import Convergent

open Convergent

def pnExample : Int :=
  let r1 : ReplicaId := 1
  let pn := runCRDT PNCounter.empty do
    PNCounter.incByM r1 4
    PNCounter.decM r1
  pn.value
-- expected: 3
```

## Sets

```lean
import Convergent

open Convergent

def orsetExample : List String :=
  let r1 : ReplicaId := 1
  let tag1 := UniqueId.new r1 0
  let tag2 := UniqueId.new r1 1
  let s1 := ORSet.apply ORSet.empty (ORSet.add "a" tag1)
  let s2 := ORSet.apply s1 (ORSet.add "a" tag2)
  let removeOp := ORSet.remove s2 "a"
  let s3 := ORSet.apply s2 removeOp
  s3.toList
-- expected: []
```

## Maps with Nested CRDTs

```lean
import Convergent

open Convergent

def ormapCounterExample : Option Int :=
  let r1 : ReplicaId := 1
  let tag := UniqueId.new r1 0
  let m : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun s => ORMap.apply s (ORMap.put "views" PNCounter.empty tag)
    |> fun s => ORMap.apply s (ORMap.update "views" tag (PNCounter.increment r1))
    |> fun s => ORMap.apply s (ORMap.update "views" tag (PNCounter.increment r1))
  m.getOne "views" |>.map (·.value)
-- expected: some 2
```

## Registers

```lean
import Convergent

open Convergent

def lwwRegisterExample : Option String :=
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r2
  let reg := LWWRegister.empty
    |> fun s => LWWRegister.apply s (LWWRegister.set "old" ts1)
    |> fun s => LWWRegister.apply s (LWWRegister.set "new" ts2)
  reg.get
-- expected: some "new"
```

```lean
import Convergent

open Convergent

def mvRegisterExample : List String :=
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let vc1 := VectorClock.inc VectorClock.empty r1
  let vc2 := VectorClock.inc VectorClock.empty r2
  let reg := MVRegister.empty
    |> fun s => MVRegister.apply s (MVRegister.set "a" vc1)
    |> fun s => MVRegister.apply s (MVRegister.set "b" vc2)
  reg.get
-- expected: ["a", "b"] in some order
```

## Sequences

```lean
import Convergent

open Convergent

def lseqExample : List String :=
  let r1 : ReplicaId := 1
  let (_, s1) := LSEQ.insertAt (LSEQ.empty : LSEQ String) r1 0 "first"
  let (_, s2) := LSEQ.insertAt s1 r1 1 "second"
  let s3 :=
    match LSEQ.deleteAt s2 0 with
    | some op => LSEQ.apply s2 op
    | none => s2
  s3.toList
-- expected: ["second"]
```

```lean
import Convergent

open Convergent

def rgaExample : List String :=
  let r1 : ReplicaId := 1
  let id1 := UniqueId.new r1 0
  let id2 := UniqueId.new r1 1
  let rga := RGA.empty
    |> fun s => RGA.apply s (RGA.insert none "a" id1)
    |> fun s => RGA.apply s (RGA.insert (some id1) "b" id2)
  rga.toList
-- expected: ["a", "b"]
```

```lean
import Convergent

open Convergent

def fugueExample : List String :=
  let r1 : ReplicaId := 1
  let (op1, f1) := Fugue.insertAt (Fugue.empty : Fugue String) r1 0 "hi"
  let f2 :=
    match op1 with
    | .insert node => Fugue.apply f1 (Fugue.delete node.id)
    | _ => f1
  f2.toList
-- expected: []
```

## Flags (Timestamp-Based)

```lean
import Convergent

open Convergent

def ewFlagExample : Bool :=
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2  -- concurrent
  let f := EWFlag.apply EWFlag.empty (EWFlag.enable tsEnable)
  let f' := EWFlag.apply f (EWFlag.disable tsDisable)
  f'.value
-- expected: true (enable wins on equal time)
```

```lean
import Convergent

open Convergent

def dwFlagExample : Bool :=
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2  -- concurrent
  let f := DWFlag.apply DWFlag.empty (DWFlag.enable tsEnable)
  let f' := DWFlag.apply f (DWFlag.disable tsDisable)
  f'.value
-- expected: false (disable wins on equal time)
```

## Serialization

```lean
import Convergent
import Convergent.Serialization

open Convergent
open Convergent.Serialization

def roundTripCounter : Option GCounter :=
  let r1 : ReplicaId := 1
  let gc := runCRDT GCounter.empty do
    GCounter.incM r1
    GCounter.incM r1
  BinarySerialize.roundTrip gc
```
