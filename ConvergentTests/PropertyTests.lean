/-
  Property-based tests for Convergent CRDTs using Plausible.
  These tests verify CRDT laws: commutativity, associativity, idempotency.
-/

import Convergent
import Plausible

namespace ConvergentTests.PropertyTests

open Plausible
open Convergent

/-! ## Equality Helpers for HashMap-based types -/

/-- Compare GCounters by value -/
def gcounterEq (a b : GCounter) : Bool :=
  a.value == b.value

/-- Compare PNCounters by value -/
def pncounterEq (a b : PNCounter) : Bool :=
  a.value == b.value

/-- Compare LWWRegisters -/
def lwwRegisterEq [BEq α] (a b : LWWRegister α) : Bool :=
  match a.value, b.value with
  | none, none => true
  | some (va, tsa), some (vb, tsb) => va == vb && tsa == tsb
  | _, _ => false

/-- Compare MVRegisters by values (order-independent) -/
def mvRegisterEq [BEq α] (a b : MVRegister α) : Bool :=
  let aVals := a.get
  let bVals := b.get
  aVals.length == bVals.length &&
  aVals.all fun v => bVals.any (· == v)

/-- Compare GSets by elements (order-independent) -/
def gsetEq [BEq α] (a b : GSet α) : Bool :=
  a.elements.length == b.elements.length &&
  a.elements.all fun e => b.contains e

/-- Compare TwoPSets by visible elements -/
def twopsetEq [BEq α] (a b : TwoPSet α) : Bool :=
  let aList := a.toList
  let bList := b.toList
  aList.length == bList.length &&
  aList.all fun e => bList.any (· == e)

/-- Compare ORSets by contained elements -/
def orsetEq [BEq α] [Hashable α] (a b : ORSet α) : Bool :=
  let aList := a.toList
  let bList := b.toList
  aList.length == bList.length &&
  aList.all fun e => b.contains e

/-- Compare LWWMaps by key-value pairs -/
def lwwMapEq [BEq κ] [Hashable κ] [BEq α] (a b : LWWMap κ α) : Bool :=
  let aList := a.toList
  let bList := b.toList
  aList.length == bList.length &&
  aList.all fun (k, v) => b.get k == some v

/-- Compare RGAs by visible content -/
def rgaEq [BEq α] (a b : RGA α) : Bool :=
  a.toList == b.toList

/-- Compare ORMaps by keys and tags (order-independent) -/
def ormapEq [BEq κ] [Hashable κ] (a b : ORMap κ α OpA) : Bool :=
  let aKeys := a.keys
  let bKeys := b.keys
  aKeys.length == bKeys.length &&
  aKeys.all fun k =>
    let aTags := a.getTags k
    let bTags := b.getTags k
    aTags.length == bTags.length &&
    aTags.all fun t => bTags.any (· == t)

/-- Compare EWFlags by enabled/disabled sets -/
def ewflagEq (a b : EWFlag) : Bool :=
  gsetEq a.enabled b.enabled && gsetEq a.disabled b.disabled

/-- Compare DWFlags by enabled/disabled sets -/
def dwflagEq (a b : DWFlag) : Bool :=
  gsetEq a.enabled b.enabled && gsetEq a.disabled b.disabled

/-- Compare LWWElementSets by contained elements -/
def lwwElementSetEq [BEq α] [Hashable α] (a b : LWWElementSet α) : Bool :=
  let aList := a.toList
  let bList := b.toList
  aList.length == bList.length &&
  aList.all fun e => b.contains e

/-- Compare PNMaps by key-value pairs -/
def pnmapEq [BEq κ] [Hashable κ] (a b : PNMap κ) : Bool :=
  let aList := a.toList
  let bList := b.toList
  aList.length == bList.length &&
  aList.all fun (k, v) => b.get k == v

/-! ## Random Generators -/

/-- Generate a small Nat in range [0, n] -/
def genSmallNat (n : Nat) : Gen Nat := do
  let x ← Gen.choose Nat 0 n (by omega)
  return x.val

/-! ## Repr Instances for Operations -/

instance : Repr GCounterOp where
  reprPrec op _ := s!"GCounterOp({op.replica})"

instance : Repr PNCounterOp where
  reprPrec op _ := match op with
    | .increment r => s!"PNCounterOp.increment({r})"
    | .decrement r => s!"PNCounterOp.decrement({r})"

instance [Repr α] : Repr (GSetOp α) where
  reprPrec op _ := s!"GSetOp({repr op.value})"

instance [Repr α] : Repr (TwoPSetOp α) where
  reprPrec op _ := match op with
    | .add v => s!"TwoPSetOp.add({repr v})"
    | .remove v => s!"TwoPSetOp.remove({repr v})"

instance [Repr α] : Repr (ORSetOp α) where
  reprPrec op _ := match op with
    | .add v t => s!"ORSetOp.add({repr v}, {repr t})"
    | .remove v ts => s!"ORSetOp.remove({repr v}, {repr ts})"

instance [Repr κ] [Repr α] : Repr (LWWMapOp κ α) where
  reprPrec op _ := match op with
    | .put k v ts => s!"LWWMapOp.put({repr k}, {repr v}, {repr ts})"
    | .delete k ts => s!"LWWMapOp.delete({repr k}, {repr ts})"

instance [Repr α] : Repr (RGAOp α) where
  reprPrec op _ := match op with
    | .insert aid v id => s!"RGAOp.insert({repr aid}, {repr v}, {repr id})"
    | .delete id => s!"RGAOp.delete({repr id})"

instance [Repr κ] [Repr α] [Repr OpA] : Repr (ORMapOp κ α OpA) where
  reprPrec op _ := match op with
    | .put k v tag => s!"ORMapOp.put({repr k}, {repr v}, {repr tag})"
    | .delete k tags => s!"ORMapOp.delete({repr k}, {repr tags})"
    | .update k tag nestedOp => s!"ORMapOp.update({repr k}, {repr tag}, {repr nestedOp})"

instance : Repr EWFlagOp where
  reprPrec op _ := match op with
    | .enable r => s!"EWFlagOp.enable({repr r})"
    | .disable r => s!"EWFlagOp.disable({repr r})"

instance : Repr DWFlagOp where
  reprPrec op _ := match op with
    | .enable r => s!"DWFlagOp.enable({repr r})"
    | .disable r => s!"DWFlagOp.disable({repr r})"

instance [Repr α] : Repr (LWWElementSetOp α) where
  reprPrec op _ := match op with
    | .add v ts => s!"LWWElementSetOp.add({repr v}, {repr ts})"
    | .remove v ts => s!"LWWElementSetOp.remove({repr v}, {repr ts})"

instance [Repr κ] : Repr (PNMapOp κ) where
  reprPrec op _ := match op with
    | .increment k r => s!"PNMapOp.increment({repr k}, {repr r})"
    | .decrement k r => s!"PNMapOp.decrement({repr k}, {repr r})"

/-! ## Shrinkable Instances -/

instance : Shrinkable ReplicaId where
  shrink r := if r.id == 0 then [] else [{ id := 0 }]

instance : Shrinkable LamportTs where
  shrink ts := if ts.time == 0 then [] else [{ ts with time := 0 }]

instance : Shrinkable VectorClock where
  shrink _ := [VectorClock.empty]

instance : Shrinkable UniqueId where
  shrink uid := if uid.seq == 0 then [] else [{ uid with seq := 0 }]

instance : Shrinkable GCounter where
  shrink _ := [GCounter.empty]

instance : Shrinkable GCounterOp where
  shrink _ := []

instance : Shrinkable PNCounter where
  shrink _ := [PNCounter.empty]

instance : Shrinkable PNCounterOp where
  shrink _ := []

instance : Shrinkable (LWWRegister α) where
  shrink _ := [LWWRegister.empty]

instance [Repr α] : Shrinkable (LWWRegisterOp α) where
  shrink _ := []

instance : Shrinkable (MVRegister α) where
  shrink _ := [MVRegister.empty]

instance [Repr α] : Shrinkable (MVRegisterOp α) where
  shrink _ := []

instance [BEq α] : Shrinkable (GSet α) where
  shrink _ := [GSet.empty]

instance : Shrinkable (GSetOp α) where
  shrink _ := []

instance [BEq α] : Shrinkable (TwoPSet α) where
  shrink _ := [TwoPSet.empty]

instance : Shrinkable (TwoPSetOp α) where
  shrink _ := []

instance [BEq α] [Hashable α] : Shrinkable (ORSet α) where
  shrink _ := [ORSet.empty]

instance : Shrinkable (ORSetOp α) where
  shrink _ := []

instance [BEq κ] [Hashable κ] : Shrinkable (LWWMap κ α) where
  shrink _ := [LWWMap.empty]

instance : Shrinkable (LWWMapOp κ α) where
  shrink _ := []

instance : Shrinkable (RGA α) where
  shrink _ := [RGA.empty]

instance : Shrinkable (RGAOp α) where
  shrink _ := []

instance [BEq κ] [Hashable κ] : Shrinkable (ORMap κ α OpA) where
  shrink _ := [ORMap.empty]

instance : Shrinkable (ORMapOp κ α OpA) where
  shrink _ := []

instance : Shrinkable EWFlag where
  shrink _ := [EWFlag.empty]

instance : Shrinkable EWFlagOp where
  shrink _ := []

instance : Shrinkable DWFlag where
  shrink _ := [DWFlag.empty]

instance : Shrinkable DWFlagOp where
  shrink _ := []

instance [BEq α] [Hashable α] : Shrinkable (LWWElementSet α) where
  shrink _ := [LWWElementSet.empty]

instance : Shrinkable (LWWElementSetOp α) where
  shrink _ := []

instance [BEq κ] [Hashable κ] : Shrinkable (PNMap κ) where
  shrink _ := [PNMap.empty]

instance : Shrinkable (PNMapOp κ) where
  shrink _ := []

/-! ## Arbitrary Instances for Core Types -/

instance : Arbitrary ReplicaId where
  arbitrary := do
    let n ← genSmallNat 4
    return { id := n }

instance : Arbitrary LamportTs where
  arbitrary := do
    let time ← genSmallNat 10
    let replica ← Arbitrary.arbitrary
    return { time, replica }

instance : Arbitrary VectorClock where
  arbitrary := do
    let numReplicas ← genSmallNat 3
    let mut vc := VectorClock.empty
    for i in [0:numReplicas] do
      let time ← genSmallNat 5
      vc := { clocks := vc.clocks.insert { id := i } time }
    return vc

instance : Arbitrary UniqueId where
  arbitrary := do
    let replica ← Arbitrary.arbitrary
    let seq ← genSmallNat 10
    return { replica, seq }

/-! ## Arbitrary Instances for Counter Types -/

instance : Arbitrary GCounter where
  arbitrary := do
    let numOps ← genSmallNat 5
    let mut gc := GCounter.empty
    for _ in [0:numOps] do
      let replica ← Arbitrary.arbitrary
      gc := GCounter.apply gc (GCounter.increment replica)
    return gc

instance : Arbitrary GCounterOp where
  arbitrary := do
    let replica ← Arbitrary.arbitrary
    return { replica }

instance : Arbitrary PNCounter where
  arbitrary := do
    let numOps ← genSmallNat 5
    let mut pn := PNCounter.empty
    for _ in [0:numOps] do
      let replica ← Arbitrary.arbitrary
      let isInc ← genSmallNat 1
      let op := if isInc == 0 then PNCounter.increment replica else PNCounter.decrement replica
      pn := PNCounter.apply pn op
    return pn

instance : Arbitrary PNCounterOp where
  arbitrary := do
    let replica ← Arbitrary.arbitrary
    let isInc ← genSmallNat 1
    return if isInc == 0 then .increment replica else .decrement replica

/-! ## Arbitrary Instances for Register Types -/

instance : Arbitrary (LWWRegister Nat) where
  arbitrary := do
    let hasValue ← genSmallNat 1
    if hasValue == 0 then
      return LWWRegister.empty
    else
      let value ← genSmallNat 100
      let ts ← Arbitrary.arbitrary
      return { value := some (value, ts) }

instance : Arbitrary (LWWRegisterOp Nat) where
  arbitrary := do
    let value ← genSmallNat 100
    let ts ← Arbitrary.arbitrary
    return { value, timestamp := ts }

instance : Arbitrary (MVRegister Nat) where
  arbitrary := do
    let numValues ← genSmallNat 2
    let mut reg := MVRegister.empty
    for _ in [0:numValues] do
      let v ← genSmallNat 100
      let vc ← Arbitrary.arbitrary
      reg := MVRegister.apply reg (MVRegister.set v vc)
    return reg

instance : Arbitrary (MVRegisterOp Nat) where
  arbitrary := do
    let value ← genSmallNat 100
    let clock ← Arbitrary.arbitrary
    return { value, clock }

/-! ## Arbitrary Instances for Set Types -/

instance : Arbitrary (GSet Nat) where
  arbitrary := do
    let numElems ← genSmallNat 5
    let mut gs := GSet.empty
    for _ in [0:numElems] do
      let v ← genSmallNat 20
      gs := GSet.apply gs (GSet.add v)
    return gs

instance : Arbitrary (GSetOp Nat) where
  arbitrary := do
    let value ← genSmallNat 20
    return { value }

instance : Arbitrary (TwoPSet Nat) where
  arbitrary := do
    let numOps ← genSmallNat 5
    let mut tps := TwoPSet.empty
    for _ in [0:numOps] do
      let v ← genSmallNat 10
      let isAdd ← genSmallNat 2
      let op := if isAdd < 2 then TwoPSet.add v else TwoPSet.remove v
      tps := TwoPSet.apply tps op
    return tps

instance : Arbitrary (TwoPSetOp Nat) where
  arbitrary := do
    let value ← genSmallNat 10
    let isAdd ← genSmallNat 1
    return if isAdd == 0 then .add value else .remove value

instance : Arbitrary (ORSet Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut os := ORSet.empty
    let mut seq := 0
    for _ in [0:numOps] do
      let v ← genSmallNat 10
      let replica ← Arbitrary.arbitrary
      let tag := UniqueId.new replica seq
      seq := seq + 1
      os := ORSet.apply os (ORSet.add v tag)
    return os

instance : Arbitrary (ORSetOp Nat) where
  arbitrary := do
    let value ← genSmallNat 10
    let tag ← Arbitrary.arbitrary
    return .add value tag

/-! ## Arbitrary Instances for Map Type -/

instance : Arbitrary (LWWMap Nat Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut m := LWWMap.empty
    for _ in [0:numOps] do
      let key ← genSmallNat 5
      let value ← genSmallNat 100
      let ts ← Arbitrary.arbitrary
      m := LWWMap.apply m (LWWMap.put key value ts)
    return m

instance : Arbitrary (LWWMapOp Nat Nat) where
  arbitrary := do
    let key ← genSmallNat 5
    let value ← genSmallNat 100
    let ts ← Arbitrary.arbitrary
    let isPut ← genSmallNat 2
    return if isPut < 2 then .put key value ts else .delete key ts

instance : Arbitrary (ORMap Nat Nat Unit) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut m : ORMap Nat Nat Unit := ORMap.empty
    let mut seq := 0
    for _ in [0:numOps] do
      let k ← genSmallNat 5
      let v ← genSmallNat 100
      let replica ← Arbitrary.arbitrary
      let tag := UniqueId.new replica seq
      seq := seq + 1
      m := ORMap.apply m (ORMap.put k v tag)
    return m

instance : Arbitrary (ORMapOp Nat Nat Unit) where
  arbitrary := do
    let k ← genSmallNat 5
    let v ← genSmallNat 100
    let tag ← Arbitrary.arbitrary
    return .put k v tag

/-! ## Arbitrary Instances for Sequence Type -/

instance : Arbitrary (RGA Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut rga := RGA.empty
    let mut lastId : Option UniqueId := none
    let mut seq := 0
    for _ in [0:numOps] do
      let value ← genSmallNat 100
      let replica ← Arbitrary.arbitrary
      let id := UniqueId.new replica seq
      seq := seq + 1
      rga := RGA.apply rga (RGA.insert lastId value id)
      lastId := some id
    return rga

instance : Arbitrary (RGAOp Nat) where
  arbitrary := do
    let value ← genSmallNat 100
    let id ← Arbitrary.arbitrary
    let isInsert ← genSmallNat 2
    if isInsert < 2 then
      return .insert none value id
    else
      return .delete id

/-! ## Arbitrary Instances for Flag Types -/

instance : Arbitrary EWFlag where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut f := EWFlag.empty
    for _ in [0:numOps] do
      let replica ← Arbitrary.arbitrary
      let isEnable ← genSmallNat 1
      let op := if isEnable == 0 then EWFlag.enable replica else EWFlag.disable replica
      f := EWFlag.apply f op
    return f

instance : Arbitrary EWFlagOp where
  arbitrary := do
    let replica ← Arbitrary.arbitrary
    let isEnable ← genSmallNat 1
    return if isEnable == 0 then .enable replica else .disable replica

instance : Arbitrary DWFlag where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut f := DWFlag.empty
    for _ in [0:numOps] do
      let replica ← Arbitrary.arbitrary
      let isEnable ← genSmallNat 1
      let op := if isEnable == 0 then DWFlag.enable replica else DWFlag.disable replica
      f := DWFlag.apply f op
    return f

instance : Arbitrary DWFlagOp where
  arbitrary := do
    let replica ← Arbitrary.arbitrary
    let isEnable ← genSmallNat 1
    return if isEnable == 0 then .enable replica else .disable replica

/-! ## Arbitrary Instances for LWWElementSet -/

instance : Arbitrary (LWWElementSet Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut set := LWWElementSet.empty
    for i in [0:numOps] do
      let v ← genSmallNat 10
      let ts ← Arbitrary.arbitrary
      let isAdd ← genSmallNat 1
      let op := if isAdd == 0 then LWWElementSet.add v ts else LWWElementSet.remove v ts
      set := LWWElementSet.apply set op
    return set

instance : Arbitrary (LWWElementSetOp Nat) where
  arbitrary := do
    let value ← genSmallNat 10
    let ts ← Arbitrary.arbitrary
    let isAdd ← genSmallNat 1
    return if isAdd == 0 then .add value ts else .remove value ts

/-! ## Arbitrary Instances for PNMap -/

instance : Arbitrary (PNMap Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut m := PNMap.empty
    for _ in [0:numOps] do
      let k ← genSmallNat 5
      let replica ← Arbitrary.arbitrary
      let isInc ← genSmallNat 1
      let op := if isInc == 0 then PNMap.increment k replica else PNMap.decrement k replica
      m := PNMap.apply m op
    return m

instance : Arbitrary (PNMapOp Nat) where
  arbitrary := do
    let key ← genSmallNat 5
    let replica ← Arbitrary.arbitrary
    let isInc ← genSmallNat 1
    return if isInc == 0 then .increment key replica else .decrement key replica

/-! ## Property Tests: Merge Laws -/

-- GCounter Merge Laws
#test ∀ (a b : GCounter), gcounterEq (GCounter.merge a b) (GCounter.merge b a)
#test ∀ (a b c : GCounter),
  gcounterEq (GCounter.merge (GCounter.merge a b) c)
             (GCounter.merge a (GCounter.merge b c))
#test ∀ (a : GCounter), gcounterEq (GCounter.merge a a) a

-- PNCounter Merge Laws
#test ∀ (a b : PNCounter), pncounterEq (PNCounter.merge a b) (PNCounter.merge b a)
#test ∀ (a b c : PNCounter),
  pncounterEq (PNCounter.merge (PNCounter.merge a b) c)
              (PNCounter.merge a (PNCounter.merge b c))
#test ∀ (a : PNCounter), pncounterEq (PNCounter.merge a a) a

-- LWWRegister Merge Laws
#test ∀ (a b : LWWRegister Nat), lwwRegisterEq (LWWRegister.merge a b) (LWWRegister.merge b a)
#test ∀ (a b c : LWWRegister Nat),
  lwwRegisterEq (LWWRegister.merge (LWWRegister.merge a b) c)
                (LWWRegister.merge a (LWWRegister.merge b c))
#test ∀ (a : LWWRegister Nat), lwwRegisterEq (LWWRegister.merge a a) a

-- MVRegister Merge Laws
#test ∀ (a b : MVRegister Nat), mvRegisterEq (MVRegister.merge a b) (MVRegister.merge b a)
#test ∀ (a b c : MVRegister Nat),
  mvRegisterEq (MVRegister.merge (MVRegister.merge a b) c)
               (MVRegister.merge a (MVRegister.merge b c))
#test ∀ (a : MVRegister Nat), mvRegisterEq (MVRegister.merge a a) a

-- GSet Merge Laws
#test ∀ (a b : GSet Nat), gsetEq (GSet.merge a b) (GSet.merge b a)
#test ∀ (a b c : GSet Nat),
  gsetEq (GSet.merge (GSet.merge a b) c)
         (GSet.merge a (GSet.merge b c))
#test ∀ (a : GSet Nat), gsetEq (GSet.merge a a) a

-- TwoPSet Merge Laws
#test ∀ (a b : TwoPSet Nat), twopsetEq (TwoPSet.merge a b) (TwoPSet.merge b a)
#test ∀ (a b c : TwoPSet Nat),
  twopsetEq (TwoPSet.merge (TwoPSet.merge a b) c)
            (TwoPSet.merge a (TwoPSet.merge b c))
#test ∀ (a : TwoPSet Nat), twopsetEq (TwoPSet.merge a a) a

-- ORSet Merge Laws
#test ∀ (a b : ORSet Nat), orsetEq (ORSet.merge a b) (ORSet.merge b a)
#test ∀ (a b c : ORSet Nat),
  orsetEq (ORSet.merge (ORSet.merge a b) c)
          (ORSet.merge a (ORSet.merge b c))
#test ∀ (a : ORSet Nat), orsetEq (ORSet.merge a a) a

-- LWWMap Merge Laws
#test ∀ (a b : LWWMap Nat Nat), lwwMapEq (LWWMap.merge a b) (LWWMap.merge b a)
#test ∀ (a b c : LWWMap Nat Nat),
  lwwMapEq (LWWMap.merge (LWWMap.merge a b) c)
           (LWWMap.merge a (LWWMap.merge b c))
#test ∀ (a : LWWMap Nat Nat), lwwMapEq (LWWMap.merge a a) a

-- RGA Merge Laws
#test ∀ (a b : RGA Nat), rgaEq (RGA.merge a b) (RGA.merge b a)
#test ∀ (a b c : RGA Nat),
  rgaEq (RGA.merge (RGA.merge a b) c)
        (RGA.merge a (RGA.merge b c))
#test ∀ (a : RGA Nat), rgaEq (RGA.merge a a) a

-- ORMap Merge Laws
#test ∀ (a b : ORMap Nat Nat Unit), ormapEq (ORMap.merge a b) (ORMap.merge b a)
#test ∀ (a b c : ORMap Nat Nat Unit),
  ormapEq (ORMap.merge (ORMap.merge a b) c)
          (ORMap.merge a (ORMap.merge b c))
#test ∀ (a : ORMap Nat Nat Unit), ormapEq (ORMap.merge a a) a

-- EWFlag Merge Laws
#test ∀ (a b : EWFlag), ewflagEq (EWFlag.merge a b) (EWFlag.merge b a)
#test ∀ (a b c : EWFlag),
  ewflagEq (EWFlag.merge (EWFlag.merge a b) c)
           (EWFlag.merge a (EWFlag.merge b c))
#test ∀ (a : EWFlag), ewflagEq (EWFlag.merge a a) a

-- DWFlag Merge Laws
#test ∀ (a b : DWFlag), dwflagEq (DWFlag.merge a b) (DWFlag.merge b a)
#test ∀ (a b c : DWFlag),
  dwflagEq (DWFlag.merge (DWFlag.merge a b) c)
           (DWFlag.merge a (DWFlag.merge b c))
#test ∀ (a : DWFlag), dwflagEq (DWFlag.merge a a) a

-- LWWElementSet Merge Laws
#test ∀ (a b : LWWElementSet Nat), lwwElementSetEq (LWWElementSet.merge a b) (LWWElementSet.merge b a)
#test ∀ (a b c : LWWElementSet Nat),
  lwwElementSetEq (LWWElementSet.merge (LWWElementSet.merge a b) c)
                  (LWWElementSet.merge a (LWWElementSet.merge b c))
#test ∀ (a : LWWElementSet Nat), lwwElementSetEq (LWWElementSet.merge a a) a

-- PNMap Merge Laws
#test ∀ (a b : PNMap Nat), pnmapEq (PNMap.merge a b) (PNMap.merge b a)
#test ∀ (a b c : PNMap Nat),
  pnmapEq (PNMap.merge (PNMap.merge a b) c)
          (PNMap.merge a (PNMap.merge b c))
#test ∀ (a : PNMap Nat), pnmapEq (PNMap.merge a a) a

/-! ## Property Tests: Apply Commutativity -/

-- GCounter apply commutes
#test ∀ (s : GCounter) (op1 op2 : GCounterOp),
  gcounterEq (GCounter.apply (GCounter.apply s op1) op2)
             (GCounter.apply (GCounter.apply s op2) op1)

-- PNCounter apply commutes
#test ∀ (s : PNCounter) (op1 op2 : PNCounterOp),
  pncounterEq (PNCounter.apply (PNCounter.apply s op1) op2)
              (PNCounter.apply (PNCounter.apply s op2) op1)

-- GSet apply commutes
#test ∀ (s : GSet Nat) (op1 op2 : GSetOp Nat),
  gsetEq (GSet.apply (GSet.apply s op1) op2)
         (GSet.apply (GSet.apply s op2) op1)

-- TwoPSet apply commutes
#test ∀ (s : TwoPSet Nat) (op1 op2 : TwoPSetOp Nat),
  twopsetEq (TwoPSet.apply (TwoPSet.apply s op1) op2)
            (TwoPSet.apply (TwoPSet.apply s op2) op1)

-- LWWRegister apply commutes
#test ∀ (s : LWWRegister Nat) (op1 op2 : LWWRegisterOp Nat),
  lwwRegisterEq (LWWRegister.apply (LWWRegister.apply s op1) op2)
                (LWWRegister.apply (LWWRegister.apply s op2) op1)

-- MVRegister apply commutes
#test ∀ (s : MVRegister Nat) (op1 op2 : MVRegisterOp Nat),
  mvRegisterEq (MVRegister.apply (MVRegister.apply s op1) op2)
               (MVRegister.apply (MVRegister.apply s op2) op1)

-- ORSet apply commutes
#test ∀ (s : ORSet Nat) (op1 op2 : ORSetOp Nat),
  orsetEq (ORSet.apply (ORSet.apply s op1) op2)
          (ORSet.apply (ORSet.apply s op2) op1)

-- LWWMap apply commutes
#test ∀ (s : LWWMap Nat Nat) (op1 op2 : LWWMapOp Nat Nat),
  lwwMapEq (LWWMap.apply (LWWMap.apply s op1) op2)
           (LWWMap.apply (LWWMap.apply s op2) op1)

-- RGA apply commutes
#test ∀ (s : RGA Nat) (op1 op2 : RGAOp Nat),
  rgaEq (RGA.apply (RGA.apply s op1) op2)
        (RGA.apply (RGA.apply s op2) op1)

-- ORMap apply commutes
#test ∀ (s : ORMap Nat Nat Unit) (op1 op2 : ORMapOp Nat Nat Unit),
  ormapEq (ORMap.apply (ORMap.apply s op1) op2)
          (ORMap.apply (ORMap.apply s op2) op1)

-- EWFlag apply commutes
#test ∀ (s : EWFlag) (op1 op2 : EWFlagOp),
  ewflagEq (EWFlag.apply (EWFlag.apply s op1) op2)
           (EWFlag.apply (EWFlag.apply s op2) op1)

-- DWFlag apply commutes
#test ∀ (s : DWFlag) (op1 op2 : DWFlagOp),
  dwflagEq (DWFlag.apply (DWFlag.apply s op1) op2)
           (DWFlag.apply (DWFlag.apply s op2) op1)

-- LWWElementSet apply commutes
#test ∀ (s : LWWElementSet Nat) (op1 op2 : LWWElementSetOp Nat),
  lwwElementSetEq (LWWElementSet.apply (LWWElementSet.apply s op1) op2)
                  (LWWElementSet.apply (LWWElementSet.apply s op2) op1)

-- PNMap apply commutes
#test ∀ (s : PNMap Nat) (op1 op2 : PNMapOp Nat),
  pnmapEq (PNMap.apply (PNMap.apply s op1) op2)
          (PNMap.apply (PNMap.apply s op2) op1)

/-! ## Property Tests: Apply Idempotency -/

-- GSet add is idempotent
#test ∀ (gs : GSet Nat) (v : Nat),
  let gs' := GSet.apply gs (GSet.add v)
  gsetEq (GSet.apply gs' (GSet.add v)) gs'

-- TwoPSet add is idempotent
#test ∀ (tps : TwoPSet Nat) (v : Nat),
  let tps' := TwoPSet.apply tps (TwoPSet.add v)
  twopsetEq (TwoPSet.apply tps' (TwoPSet.add v)) tps'

-- TwoPSet remove is idempotent
#test ∀ (tps : TwoPSet Nat) (v : Nat),
  let tps' := TwoPSet.apply tps (TwoPSet.remove v)
  twopsetEq (TwoPSet.apply tps' (TwoPSet.remove v)) tps'

-- LWWRegister set is idempotent
#test ∀ (reg : LWWRegister Nat) (op : LWWRegisterOp Nat),
  let reg' := LWWRegister.apply reg op
  lwwRegisterEq (LWWRegister.apply reg' op) reg'

-- MVRegister set is idempotent
#test ∀ (reg : MVRegister Nat) (op : MVRegisterOp Nat),
  let reg' := MVRegister.apply reg op
  mvRegisterEq (MVRegister.apply reg' op) reg'

-- ORSet add is idempotent
#test ∀ (os : ORSet Nat) (v : Nat) (tag : UniqueId),
  let os' := ORSet.apply os (ORSet.add v tag)
  orsetEq (ORSet.apply os' (ORSet.add v tag)) os'

-- ORSet remove is idempotent
#test ∀ (os : ORSet Nat) (v : Nat),
  let op := ORSet.remove os v
  let os' := ORSet.apply os op
  orsetEq (ORSet.apply os' op) os'

-- LWWMap put is idempotent
#test ∀ (m : LWWMap Nat Nat) (k v : Nat) (ts : LamportTs),
  let m' := LWWMap.apply m (LWWMap.put k v ts)
  lwwMapEq (LWWMap.apply m' (LWWMap.put k v ts)) m'

-- LWWMap delete is idempotent
#test ∀ (m : LWWMap Nat Nat) (k : Nat) (ts : LamportTs),
  let m' := LWWMap.apply m (LWWMap.delete k ts)
  lwwMapEq (LWWMap.apply m' (LWWMap.delete k ts)) m'

-- RGA insert is idempotent
#test ∀ (rga : RGA Nat) (v : Nat) (id : UniqueId),
  let rga' := RGA.apply rga (RGA.insert none v id)
  rgaEq (RGA.apply rga' (RGA.insert none v id)) rga'

-- RGA delete is idempotent
#test ∀ (rga : RGA Nat) (id : UniqueId),
  let rga' := RGA.apply rga (RGA.delete id)
  rgaEq (RGA.apply rga' (RGA.delete id)) rga'

-- ORMap put is idempotent
#test ∀ (m : ORMap Nat Nat Unit) (k v : Nat) (tag : UniqueId),
  let m' := ORMap.apply m (ORMap.put k v tag)
  ormapEq (ORMap.apply m' (ORMap.put k v tag)) m'

-- ORMap delete is idempotent
#test ∀ (m : ORMap Nat Nat Unit) (k : Nat),
  let op := ORMap.delete m k
  let m' := ORMap.apply m op
  ormapEq (ORMap.apply m' op) m'

-- EWFlag enable is idempotent
#test ∀ (f : EWFlag) (r : ReplicaId),
  let f' := EWFlag.apply f (EWFlag.enable r)
  ewflagEq (EWFlag.apply f' (EWFlag.enable r)) f'

-- EWFlag disable is idempotent
#test ∀ (f : EWFlag) (r : ReplicaId),
  let f' := EWFlag.apply f (EWFlag.disable r)
  ewflagEq (EWFlag.apply f' (EWFlag.disable r)) f'

-- DWFlag enable is idempotent
#test ∀ (f : DWFlag) (r : ReplicaId),
  let f' := DWFlag.apply f (DWFlag.enable r)
  dwflagEq (DWFlag.apply f' (DWFlag.enable r)) f'

-- DWFlag disable is idempotent
#test ∀ (f : DWFlag) (r : ReplicaId),
  let f' := DWFlag.apply f (DWFlag.disable r)
  dwflagEq (DWFlag.apply f' (DWFlag.disable r)) f'

-- LWWElementSet add is idempotent
#test ∀ (s : LWWElementSet Nat) (v : Nat) (ts : LamportTs),
  let s' := LWWElementSet.apply s (LWWElementSet.add v ts)
  lwwElementSetEq (LWWElementSet.apply s' (LWWElementSet.add v ts)) s'

-- LWWElementSet remove is idempotent
#test ∀ (s : LWWElementSet Nat) (v : Nat) (ts : LamportTs),
  let s' := LWWElementSet.apply s (LWWElementSet.remove v ts)
  lwwElementSetEq (LWWElementSet.apply s' (LWWElementSet.remove v ts)) s'

/-! ## Property Tests: Type-Specific Properties -/

-- GCounter value is monotonically non-decreasing
#test ∀ (gc : GCounter) (op : GCounterOp),
  let gc' := GCounter.apply gc op
  gc'.value >= gc.value

-- PNCounter increment increases value
#test ∀ (pn : PNCounter) (r : ReplicaId),
  let pn' := PNCounter.apply pn (PNCounter.increment r)
  pn'.value == pn.value + 1

-- PNCounter decrement decreases value
#test ∀ (pn : PNCounter) (r : ReplicaId),
  let pn' := PNCounter.apply pn (PNCounter.decrement r)
  pn'.value == pn.value - 1

-- GSet contains element after add
#test ∀ (gs : GSet Nat) (v : Nat),
  let gs' := GSet.apply gs (GSet.add v)
  gs'.contains v

-- TwoPSet: once removed, cannot re-add
#test ∀ (v : Nat),
  let tps := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.add v)
    |> fun s => TwoPSet.apply s (TwoPSet.remove v)
    |> fun s => TwoPSet.apply s (TwoPSet.add v)
  !tps.contains v

-- ORSet contains element after add
#test ∀ (v : Nat) (tag : UniqueId),
  let os := ORSet.apply ORSet.empty (ORSet.add v tag)
  os.contains v

-- LWWMap contains key after put
#test ∀ (k v : Nat) (ts : LamportTs),
  let m := LWWMap.apply LWWMap.empty (LWWMap.put k v ts)
  m.contains k

-- RGA contains ID after insert
#test ∀ (v : Nat) (id : UniqueId),
  let rga := RGA.apply RGA.empty (RGA.insert none v id)
  rga.containsId id

-- RGA delete makes element invisible but keeps ID
#test ∀ (v : Nat) (id : UniqueId),
  let rga := RGA.apply RGA.empty (RGA.insert none v id)
  let rga' := RGA.apply rga (RGA.delete id)
  rga'.containsId id && rga'.length == 0

-- LWWRegister: later timestamp wins
#test ∀ (v1 v2 : Nat) (r1 r2 : ReplicaId),
  let ts1 : LamportTs := { time := 1, replica := r1 }
  let ts2 : LamportTs := { time := 2, replica := r2 }
  let reg := LWWRegister.apply LWWRegister.empty (LWWRegister.set v1 ts1)
  let reg' := LWWRegister.apply reg (LWWRegister.set v2 ts2)
  reg'.get == some v2

-- LWWMap: later timestamp wins for same key
#test ∀ (k v1 v2 : Nat) (r1 r2 : ReplicaId),
  let ts1 : LamportTs := { time := 1, replica := r1 }
  let ts2 : LamportTs := { time := 2, replica := r2 }
  let m := LWWMap.apply LWWMap.empty (LWWMap.put k v1 ts1)
  let m' := LWWMap.apply m (LWWMap.put k v2 ts2)
  m'.get k == some v2

-- MVRegister: dominated value is removed (later clock dominates earlier)
#test ∀ (v1 v2 : Nat) (r : ReplicaId),
  let vc1 := VectorClock.inc VectorClock.empty r
  let vc2 := VectorClock.inc vc1 r  -- vc2 dominates vc1
  let reg := MVRegister.apply MVRegister.empty (MVRegister.set v1 vc1)
  let reg' := MVRegister.apply reg (MVRegister.set v2 vc2)
  reg'.get == [v2]

-- MVRegister: concurrent values are preserved (neither clock dominates)
#test ∀ (v1 v2 : Nat),
  let r1 : ReplicaId := { id := 1 }
  let r2 : ReplicaId := { id := 2 }
  let vc1 := VectorClock.inc VectorClock.empty r1
  let vc2 := VectorClock.inc VectorClock.empty r2
  let reg := MVRegister.apply MVRegister.empty (MVRegister.set v1 vc1)
  let reg' := MVRegister.apply reg (MVRegister.set v2 vc2)
  -- Both values should be present (order may vary)
  reg'.get.length == 2 && reg'.get.any (· == v1) && reg'.get.any (· == v2)

-- ORSet: can re-add after remove (with new tag)
#test ∀ (v : Nat),
  let r : ReplicaId := { id := 1 }
  let tag1 := UniqueId.new r 1
  let tag2 := UniqueId.new r 2
  let os := ORSet.apply ORSet.empty (ORSet.add v tag1)
  let removeOp := ORSet.remove os v
  let os' := ORSet.apply os removeOp
  let os'' := ORSet.apply os' (ORSet.add v tag2)
  os''.contains v

-- ORSet: remove then add results in element present (add-wins semantics)
#test ∀ (v : Nat),
  let r : ReplicaId := { id := 1 }
  let tag := UniqueId.new r 1
  -- Remove on empty set (no observed tags), then add
  let removeOp : ORSetOp Nat := .remove v []
  let os := ORSet.apply ORSet.empty removeOp
  let os' := ORSet.apply os (ORSet.add v tag)
  os'.contains v

-- GCounter: increment adds exactly 1
#test ∀ (gc : GCounter) (r : ReplicaId),
  let gc' := GCounter.apply gc (GCounter.increment r)
  gc'.value == gc.value + 1

-- RGA: concurrent inserts at same position are ordered by ID
#test ∀ (v1 v2 : Nat),
  let r1 : ReplicaId := { id := 1 }
  let r2 : ReplicaId := { id := 2 }
  let id1 := UniqueId.new r1 1
  let id2 := UniqueId.new r2 1
  -- Both insert at start, ID ordering determines position
  let rga := RGA.apply RGA.empty (RGA.insert none v1 id1)
  let rga' := RGA.apply rga (RGA.insert none v2 id2)
  -- Lower ID (r1) comes first due to ID-based ordering
  rga'.toList == [v1, v2]

-- ORMap: contains key after put
#test ∀ (k v : Nat) (tag : UniqueId),
  let m : ORMap Nat Nat Unit := ORMap.apply ORMap.empty (ORMap.put k v tag)
  m.contains k

-- ORMap: get returns value after put
#test ∀ (k v : Nat) (tag : UniqueId),
  let m : ORMap Nat Nat Unit := ORMap.apply ORMap.empty (ORMap.put k v tag)
  m.get k == [v]

-- ORMap: can re-add after delete (with new tag)
#test ∀ (k v : Nat),
  let r : ReplicaId := { id := 1 }
  let tag1 := UniqueId.new r 1
  let tag2 := UniqueId.new r 2
  let m : ORMap Nat Nat Unit := ORMap.apply ORMap.empty (ORMap.put k v tag1)
  let deleteOp := ORMap.delete m k
  let m' := ORMap.apply m deleteOp
  let m'' := ORMap.apply m' (ORMap.put k v tag2)
  m''.contains k

-- EWFlag: empty is false
#test EWFlag.empty.value == false

-- EWFlag: enable makes true
#test ∀ (r : ReplicaId),
  let f := EWFlag.apply EWFlag.empty (EWFlag.enable r)
  f.value == true

-- EWFlag: enable-wins (enable + disable = true)
#test ∀ (r1 r2 : ReplicaId),
  let f := EWFlag.empty
    |> fun s => EWFlag.apply s (EWFlag.enable r1)
    |> fun s => EWFlag.apply s (EWFlag.disable r2)
  f.value == true

-- DWFlag: empty is false
#test DWFlag.empty.value == false

-- DWFlag: enable makes true (when no disables)
#test ∀ (r : ReplicaId),
  let f := DWFlag.apply DWFlag.empty (DWFlag.enable r)
  f.value == true

-- DWFlag: disable-wins (enable + disable = false)
#test ∀ (r1 r2 : ReplicaId),
  let f := DWFlag.empty
    |> fun s => DWFlag.apply s (DWFlag.enable r1)
    |> fun s => DWFlag.apply s (DWFlag.disable r2)
  f.value == false

-- LWWElementSet: later timestamp wins (add with higher ts)
#test ∀ (v : Nat) (r1 r2 : ReplicaId),
  let ts1 : LamportTs := { time := 1, replica := r1 }
  let ts2 : LamportTs := { time := 2, replica := r2 }
  let set := LWWElementSet.empty
    |> fun s => LWWElementSet.apply s (LWWElementSet.remove v ts1)
    |> fun s => LWWElementSet.apply s (LWWElementSet.add v ts2)
  set.contains v

-- LWWElementSet: later timestamp wins (remove with higher ts)
#test ∀ (v : Nat) (r1 r2 : ReplicaId),
  let ts1 : LamportTs := { time := 1, replica := r1 }
  let ts2 : LamportTs := { time := 2, replica := r2 }
  let set := LWWElementSet.empty
    |> fun s => LWWElementSet.apply s (LWWElementSet.add v ts1)
    |> fun s => LWWElementSet.apply s (LWWElementSet.remove v ts2)
  !set.contains v

-- LWWElementSet: can re-add after remove (with newer timestamp)
#test ∀ (v : Nat) (r : ReplicaId),
  let ts1 : LamportTs := { time := 1, replica := r }
  let ts2 : LamportTs := { time := 2, replica := r }
  let ts3 : LamportTs := { time := 3, replica := r }
  let set := LWWElementSet.empty
    |> fun s => LWWElementSet.apply s (LWWElementSet.add v ts1)
    |> fun s => LWWElementSet.apply s (LWWElementSet.remove v ts2)
    |> fun s => LWWElementSet.apply s (LWWElementSet.add v ts3)
  set.contains v

-- LWWElementSet: add contains element
#test ∀ (v : Nat) (ts : LamportTs),
  let set := LWWElementSet.apply LWWElementSet.empty (LWWElementSet.add v ts)
  set.contains v

-- PNMap: increment adds exactly 1
#test ∀ (m : PNMap Nat) (k : Nat) (r : ReplicaId),
  let m' := PNMap.apply m (PNMap.increment k r)
  m'.get k == m.get k + 1

-- PNMap: decrement subtracts exactly 1
#test ∀ (m : PNMap Nat) (k : Nat) (r : ReplicaId),
  let m' := PNMap.apply m (PNMap.decrement k r)
  m'.get k == m.get k - 1

/-! ## Property Tests: Monotonicity -/

-- GSet elements are never removed (add element, apply another op, element still there)
#test ∀ (gs : GSet Nat) (v : Nat) (op : GSetOp Nat),
  let gs' := GSet.apply gs (GSet.add v)
  let gs'' := GSet.apply gs' op
  gs''.contains v

-- TwoPSet added set never shrinks (if element added successfully, it stays in added set)
#test ∀ (tps : TwoPSet Nat) (v : Nat) (op : TwoPSetOp Nat),
  let tps' := TwoPSet.apply tps (TwoPSet.add v)
  -- Only test if v was actually added (not blocked by tombstone)
  tps'.added.contains v → (TwoPSet.apply tps' op).added.contains v

-- TwoPSet removed set never shrinks (remove element, apply another op, still in removed set)
#test ∀ (tps : TwoPSet Nat) (v : Nat) (op : TwoPSetOp Nat),
  let tps' := TwoPSet.apply tps (TwoPSet.remove v)
  let tps'' := TwoPSet.apply tps' op
  tps''.removed.contains v

/-! ## Property Tests: Convergence -/

-- Convergence: same ops in different order produce same result

-- GCounter convergence (3 ops)
#test ∀ (gc : GCounter) (op1 op2 op3 : GCounterOp),
  let forward := GCounter.apply (GCounter.apply (GCounter.apply gc op1) op2) op3
  let reverse := GCounter.apply (GCounter.apply (GCounter.apply gc op3) op2) op1
  gcounterEq forward reverse

-- PNCounter convergence (3 ops)
#test ∀ (pn : PNCounter) (op1 op2 op3 : PNCounterOp),
  let forward := PNCounter.apply (PNCounter.apply (PNCounter.apply pn op1) op2) op3
  let reverse := PNCounter.apply (PNCounter.apply (PNCounter.apply pn op3) op2) op1
  pncounterEq forward reverse

-- LWWRegister convergence (3 ops)
#test ∀ (reg : LWWRegister Nat) (op1 op2 op3 : LWWRegisterOp Nat),
  let forward := LWWRegister.apply (LWWRegister.apply (LWWRegister.apply reg op1) op2) op3
  let reverse := LWWRegister.apply (LWWRegister.apply (LWWRegister.apply reg op3) op2) op1
  lwwRegisterEq forward reverse

-- MVRegister convergence (3 ops)
#test ∀ (reg : MVRegister Nat) (op1 op2 op3 : MVRegisterOp Nat),
  let forward := MVRegister.apply (MVRegister.apply (MVRegister.apply reg op1) op2) op3
  let reverse := MVRegister.apply (MVRegister.apply (MVRegister.apply reg op3) op2) op1
  mvRegisterEq forward reverse

-- GSet convergence (3 ops)
#test ∀ (gs : GSet Nat) (op1 op2 op3 : GSetOp Nat),
  let forward := GSet.apply (GSet.apply (GSet.apply gs op1) op2) op3
  let reverse := GSet.apply (GSet.apply (GSet.apply gs op3) op2) op1
  gsetEq forward reverse

-- TwoPSet convergence (3 ops)
#test ∀ (tps : TwoPSet Nat) (op1 op2 op3 : TwoPSetOp Nat),
  let forward := TwoPSet.apply (TwoPSet.apply (TwoPSet.apply tps op1) op2) op3
  let reverse := TwoPSet.apply (TwoPSet.apply (TwoPSet.apply tps op3) op2) op1
  twopsetEq forward reverse

-- ORSet convergence (3 ops)
#test ∀ (os : ORSet Nat) (op1 op2 op3 : ORSetOp Nat),
  let forward := ORSet.apply (ORSet.apply (ORSet.apply os op1) op2) op3
  let reverse := ORSet.apply (ORSet.apply (ORSet.apply os op3) op2) op1
  orsetEq forward reverse

-- LWWMap convergence (3 ops)
#test ∀ (m : LWWMap Nat Nat) (op1 op2 op3 : LWWMapOp Nat Nat),
  let forward := LWWMap.apply (LWWMap.apply (LWWMap.apply m op1) op2) op3
  let reverse := LWWMap.apply (LWWMap.apply (LWWMap.apply m op3) op2) op1
  lwwMapEq forward reverse

-- RGA convergence (3 ops)
#test ∀ (rga : RGA Nat) (op1 op2 op3 : RGAOp Nat),
  let forward := RGA.apply (RGA.apply (RGA.apply rga op1) op2) op3
  let reverse := RGA.apply (RGA.apply (RGA.apply rga op3) op2) op1
  rgaEq forward reverse

-- ORMap convergence (3 ops)
#test ∀ (m : ORMap Nat Nat Unit) (op1 op2 op3 : ORMapOp Nat Nat Unit),
  let forward := ORMap.apply (ORMap.apply (ORMap.apply m op1) op2) op3
  let reverse := ORMap.apply (ORMap.apply (ORMap.apply m op3) op2) op1
  ormapEq forward reverse

-- EWFlag convergence (3 ops)
#test ∀ (f : EWFlag) (op1 op2 op3 : EWFlagOp),
  let forward := EWFlag.apply (EWFlag.apply (EWFlag.apply f op1) op2) op3
  let reverse := EWFlag.apply (EWFlag.apply (EWFlag.apply f op3) op2) op1
  ewflagEq forward reverse

-- DWFlag convergence (3 ops)
#test ∀ (f : DWFlag) (op1 op2 op3 : DWFlagOp),
  let forward := DWFlag.apply (DWFlag.apply (DWFlag.apply f op1) op2) op3
  let reverse := DWFlag.apply (DWFlag.apply (DWFlag.apply f op3) op2) op1
  dwflagEq forward reverse

-- LWWElementSet convergence (3 ops)
#test ∀ (s : LWWElementSet Nat) (op1 op2 op3 : LWWElementSetOp Nat),
  let forward := LWWElementSet.apply (LWWElementSet.apply (LWWElementSet.apply s op1) op2) op3
  let reverse := LWWElementSet.apply (LWWElementSet.apply (LWWElementSet.apply s op3) op2) op1
  lwwElementSetEq forward reverse

-- PNMap convergence (3 ops)
#test ∀ (m : PNMap Nat) (op1 op2 op3 : PNMapOp Nat),
  let forward := PNMap.apply (PNMap.apply (PNMap.apply m op1) op2) op3
  let reverse := PNMap.apply (PNMap.apply (PNMap.apply m op3) op2) op1
  pnmapEq forward reverse

end ConvergentTests.PropertyTests
