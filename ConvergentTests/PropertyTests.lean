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

/-- Compare lists as sets (order-independent, assumes no duplicates) -/
def listSetEq [BEq α] (a b : List α) : Bool :=
  a.length == b.length &&
  a.all fun x => b.any (· == x)

/-- Compare lists of pairs as sets (order-independent, assumes no duplicates) -/
def pairListSetEq [BEq α] [BEq β] (a b : List (α × β)) : Bool :=
  a.length == b.length &&
  a.all fun (x, y) => b.any fun (x2, y2) => x == x2 && y == y2

/-- Union of keys (order-independent) -/
def unionKeys [BEq κ] (a b : List κ) : List κ :=
  (a ++ b).foldl (init := []) fun acc k =>
    if acc.any (· == k) then acc else k :: acc

/-- Compare MVRegisters by values and vector clocks (order-independent) -/
def mvRegisterStateEq [BEq α] (a b : MVRegister α) : Bool :=
  pairListSetEq a.getWithClocks b.getWithClocks

/-- Compare GSets by elements (order-independent) -/
def gsetEq [BEq α] [Hashable α] (a b : GSet α) : Bool :=
  a.size == b.size &&
  a.toList.all fun e => b.contains e

/-- Compare TwoPSets by visible elements -/
def twopsetEq [BEq α] [Hashable α] (a b : TwoPSet α) : Bool :=
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

/-- Compare ORSets by tags (state-level, order-independent) -/
def orsetStateEq [BEq α] [Hashable α] (a b : ORSet α) : Bool :=
  let aKeys := a.elements.toList.map Prod.fst
  let bKeys := b.elements.toList.map Prod.fst
  let keys := unionKeys aKeys bKeys
  keys.all fun k => listSetEq (a.getTags k) (b.getTags k)

/-- Compare LWWMaps by key-value pairs -/
def lwwMapEq [BEq κ] [Hashable κ] [BEq α] (a b : LWWMap κ α) : Bool :=
  let aList := a.toList
  let bList := b.toList
  aList.length == bList.length &&
  aList.all fun (k, v) => b.get k == some v

/-- Compare LWWMaps by value and timestamp (state-level) -/
def lwwMapStateEq [BEq κ] [Hashable κ] [BEq α] (a b : LWWMap κ α) : Bool :=
  let aKeys := a.entries.toList.map Prod.fst
  let bKeys := b.entries.toList.map Prod.fst
  let keys := unionKeys aKeys bKeys
  keys.all fun k =>
    match a.entries[k]?, b.entries[k]? with
    | none, none => true
    | some (va, tsa), some (vb, tsb) => va == vb && tsa == tsb
    | _, _ => false

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

/-- Compare ORMaps by full entries (state-level, order-independent) -/
def ormapStateEq [BEq κ] [Hashable κ] [BEq α] (a b : ORMap κ α OpA) : Bool :=
  let keys := unionKeys a.keys b.keys
  keys.all fun k => pairListSetEq (a.getEntries k) (b.getEntries k)

/-- ORMap entries are consistent if identical tags map to identical values. -/
def ormapEntriesConsistent [BEq α] (entries : List (α × UniqueId)) : Bool :=
  entries.all fun (v, t) =>
    entries.all fun (v2, t2) => if t == t2 then v == v2 else true

/-- ORMap is well-formed if tags per key are consistent. -/
def ormapWellFormed [BEq κ] [Hashable κ] [BEq α] (m : ORMap κ α OpA) : Bool :=
  m.keys.all fun k => ormapEntriesConsistent (m.getEntries k)

/-- ORMap ops are compatible if duplicate puts with same key/tag agree on value. -/
def ormapOpsCompatible [BEq κ] [BEq α] (op1 op2 : ORMapOp κ α OpA) : Bool :=
  match op1, op2 with
  | .put k1 v1 t1, .put k2 v2 t2 =>
    if k1 == k2 && t1 == t2 then v1 == v2 else true
  | _, _ => true

/-- ORMap states are compatible if identical tags map to identical values. -/
def ormapCompatible [BEq κ] [Hashable κ] [BEq α] (a b : ORMap κ α OpA) : Bool :=
  let keys := unionKeys a.keys b.keys
  keys.all fun k =>
    let entriesA := a.getEntries k
    let entriesB := b.getEntries k
    entriesA.all fun (vA, tA) =>
      entriesB.all fun (vB, tB) => if tA == tB then vA == vB else true

/-- ORMap op is compatible with state if existing tag/value pairs are consistent. -/
def ormapOpCompatibleWithState [BEq κ] [Hashable κ] [BEq α] (m : ORMap κ α OpA) (op : ORMapOp κ α OpA) : Bool :=
  match op with
  | .put k v tag =>
    let entries := m.getEntries k
    entries.all fun (v2, t2) => if t2 == tag then v2 == v else true
  | _ => true

/-- Fugue ops are compatible if duplicate inserts with the same ID agree. -/
def fugueOpsCompatible [BEq α] (op1 op2 : FugueOp α) : Bool :=
  match op1, op2 with
  | .insert n1, .insert n2 =>
    if n1.id == n2.id then n1 == n2 else true
  | _, _ => true

/-- Fugue op is compatible with state if inserts don't conflict with existing nodes. -/
def fugueOpCompatibleWithState [BEq α] (f : Fugue α) (op : FugueOp α) : Bool :=
  match op with
  | .insert node =>
    match f.getNode node.id with
    | none => true
    | some existing =>
      if existing.value.isNone then true else existing == node
  | _ => true

/-- Compare EWFlags by last enable/disable timestamps. -/
def ewflagEq (a b : EWFlag) : Bool :=
  a.lastEnable == b.lastEnable && a.lastDisable == b.lastDisable

/-- Compare DWFlags by enabled/disabled sets -/
def dwflagEq (a b : DWFlag) : Bool :=
  a.lastEnable == b.lastEnable && a.lastDisable == b.lastDisable

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

/-- Compare LSEQs by visible content -/
def lseqEq [BEq α] (a b : LSEQ α) : Bool :=
  a.toList == b.toList

/-- Compare Fugues by visible content -/
def fugueEq [BEq α] (a b : Fugue α) : Bool :=
  a.toList == b.toList

/-- Compare TwoPGraphs by vertices and edges -/
def twopgraphEq [BEq V] [Hashable V] (a b : TwoPGraph V) : Bool :=
  let aVerts := a.getVertices
  let bVerts := b.getVertices
  let aEdges := a.getEdges
  let bEdges := b.getEdges
  aVerts.length == bVerts.length &&
  aVerts.all (fun v => b.containsVertex v) &&
  aEdges.length == bEdges.length &&
  aEdges.all (fun e => b.containsEdge e.1 e.2)

/-! ## Random Generators -/

/-- Generate a small Nat in range [0, n] -/
def genSmallNat (n : Nat) : Gen Nat := do
  let x ← Gen.choose Nat 0 n (by omega)
  return x.val

/-! ## Repr Instances for Operations -/

instance : Repr GCounterOp where
  reprPrec op _ := s!"GCounterOp({op.replica}, {op.amount})"

instance : Repr PNCounterOp where
  reprPrec op _ := match op with
    | .increment r n => s!"PNCounterOp.increment({r}, {n})"
    | .decrement r n => s!"PNCounterOp.decrement({r}, {n})"

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
    | .enable ts => s!"EWFlagOp.enable({repr ts})"
    | .disable ts => s!"EWFlagOp.disable({repr ts})"

instance : Repr DWFlagOp where
  reprPrec op _ := match op with
    | .enable ts => s!"DWFlagOp.enable({repr ts})"
    | .disable ts => s!"DWFlagOp.disable({repr ts})"

instance [Repr α] : Repr (LWWElementSetOp α) where
  reprPrec op _ := match op with
    | .add v ts => s!"LWWElementSetOp.add({repr v}, {repr ts})"
    | .remove v ts => s!"LWWElementSetOp.remove({repr v}, {repr ts})"

instance [Repr κ] : Repr (PNMapOp κ) where
  reprPrec op _ := match op with
    | .increment k r => s!"PNMapOp.increment({repr k}, {repr r})"
    | .decrement k r => s!"PNMapOp.decrement({repr k}, {repr r})"

instance [Repr α] : Repr (LSEQOp α) where
  reprPrec op _ := match op with
    | .insert id v => s!"LSEQOp.insert({repr id}, {repr v})"
    | .delete id => s!"LSEQOp.delete({repr id})"

instance [Repr V] : Repr (TwoPGraphOp V) where
  reprPrec op _ := match op with
    | .addVertex v => s!"TwoPGraphOp.addVertex({repr v})"
    | .removeVertex v => s!"TwoPGraphOp.removeVertex({repr v})"
    | .addEdge a b => s!"TwoPGraphOp.addEdge({repr a}, {repr b})"
    | .removeEdge a b => s!"TwoPGraphOp.removeEdge({repr a}, {repr b})"

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

instance [BEq α] [Hashable α] : Shrinkable (GSet α) where
  shrink _ := [GSet.empty]

instance : Shrinkable (GSetOp α) where
  shrink _ := []

instance [BEq α] [Hashable α] : Shrinkable (TwoPSet α) where
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

instance : Shrinkable LSEQLevel where
  shrink _ := []

instance : Shrinkable LSEQId where
  shrink _ := [{ levels := [] }]

instance : Shrinkable (LSEQ α) where
  shrink _ := [LSEQ.empty]

instance : Shrinkable (LSEQOp α) where
  shrink _ := []

instance : Shrinkable FugueId where
  shrink _ := []

instance : Shrinkable FugueSide where
  shrink _ := []

instance : Shrinkable (FugueNode α) where
  shrink _ := []

instance : Shrinkable (Fugue α) where
  shrink _ := [Fugue.empty]

instance : Shrinkable (FugueOp α) where
  shrink _ := []

instance [BEq V] [Hashable V] : Shrinkable (TwoPGraph V) where
  shrink _ := [TwoPGraph.empty]

instance : Shrinkable (TwoPGraphOp V) where
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
    let amount ← genSmallNat 5
    return { replica, amount := amount + 1 }

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
    let amount ← genSmallNat 5
    let isInc ← genSmallNat 1
    return if isInc == 0 then .increment replica (amount + 1) else .decrement replica (amount + 1)

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
      let ts ← Arbitrary.arbitrary
      let isEnable ← genSmallNat 1
      let op := if isEnable == 0 then EWFlag.enable ts else EWFlag.disable ts
      f := EWFlag.apply f op
    return f

instance : Arbitrary EWFlagOp where
  arbitrary := do
    let ts ← Arbitrary.arbitrary
    let isEnable ← genSmallNat 1
    return if isEnable == 0 then .enable ts else .disable ts

instance : Arbitrary DWFlag where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut f := DWFlag.empty
    for _ in [0:numOps] do
      let ts ← Arbitrary.arbitrary
      let isEnable ← genSmallNat 1
      let op := if isEnable == 0 then DWFlag.enable ts else DWFlag.disable ts
      f := DWFlag.apply f op
    return f

instance : Arbitrary DWFlagOp where
  arbitrary := do
    let ts ← Arbitrary.arbitrary
    let isEnable ← genSmallNat 1
    return if isEnable == 0 then .enable ts else .disable ts

/-! ## Arbitrary Instances for LWWElementSet -/

instance : Arbitrary (LWWElementSet Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut set := LWWElementSet.empty
    for _ in [0:numOps] do
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

/-! ## Arbitrary Instances for LSEQ -/

instance : Arbitrary LSEQLevel where
  arbitrary := do
    let pos ← genSmallNat 15  -- Within base depth 0 (16)
    let site ← Arbitrary.arbitrary
    return { pos, site }

instance : Arbitrary LSEQId where
  arbitrary := do
    let numLevels ← genSmallNat 2
    let mut levels := []
    for _ in [0:numLevels + 1] do
      let level ← Arbitrary.arbitrary
      levels := levels ++ [level]
    return { levels }

instance : Arbitrary (LSEQ Nat) where
  arbitrary := do
    let numOps ← genSmallNat 4
    let mut lseq := LSEQ.empty
    let replica ← Arbitrary.arbitrary
    for i in [0:numOps] do
      let value ← genSmallNat 100
      let (_, lseq') := LSEQ.insertAt lseq replica i value
      lseq := lseq'
    return lseq

instance : Arbitrary (LSEQOp Nat) where
  arbitrary := do
    let id ← Arbitrary.arbitrary
    let value ← genSmallNat 100
    let isInsert ← genSmallNat 2
    if isInsert < 2 then
      return .insert id value
    else
      return .delete id

/-! ## Arbitrary Instances for Fugue -/

instance : Arbitrary FugueId where
  arbitrary := do
    let replica ← Arbitrary.arbitrary
    let counter ← genSmallNat 10
    return { replica, counter }

instance : Arbitrary FugueSide where
  arbitrary := do
    let choice ← genSmallNat 1
    return if choice == 0 then .left else .right

instance : Arbitrary (FugueNode Nat) where
  arbitrary := do
    -- Generate simple nodes with unique IDs to avoid conflicts
    let replica ← Arbitrary.arbitrary
    let counter ← genSmallNat 100
    let uniqueCounter := counter + 2000  -- Offset to avoid conflicts
    let id := FugueId.mk replica uniqueCounter
    let value ← genSmallNat 100
    let hasValue ← genSmallNat 3
    return {
      id
      value := if hasValue < 3 then some value else none
      parent := none
      side := .right
      leftOrigin := none
      rightOrigin := none
    }

instance : Arbitrary (Fugue Nat) where
  arbitrary := do
    let numOps ← genSmallNat 3
    let mut fugue := Fugue.empty
    -- Use a large random replica ID to ensure disjoint replicas between instances
    -- Range of 10 million makes collision probability < 0.1% even with many tests
    let replicaId ← Gen.choose Nat 0 10000000 (by omega)
    let replica : ReplicaId := { id := replicaId.val }
    for i in [0:numOps] do
      let value ← genSmallNat 100
      let (_, fugue') := Fugue.insertAt fugue replica i value
      fugue := fugue'
    return fugue

instance : Arbitrary (FugueOp Nat) where
  arbitrary := do
    -- Generate unique ID with high counter to avoid conflicts
    let replica ← Arbitrary.arbitrary
    let counter ← genSmallNat 100
    let uniqueCounter := counter + 1000  -- Offset to avoid conflicts with state
    let id := FugueId.mk replica uniqueCounter
    let value ← genSmallNat 100
    let isInsert ← genSmallNat 2
    if isInsert < 2 then
      -- Create a node with unique ID and minimal structure
      let node : FugueNode Nat := {
        id := id
        value := some value
        parent := none
        side := .right
        leftOrigin := none
        rightOrigin := none
      }
      return .insert node
    else
      return .delete id

/-! ## Arbitrary Instances for TwoPGraph -/

instance : Arbitrary (TwoPGraph Nat) where
  arbitrary := do
    let numVertices ← genSmallNat 4
    let numEdges ← genSmallNat 3
    let mut g := TwoPGraph.empty
    -- Add vertices
    for _ in [0:numVertices] do
      let v ← genSmallNat 10
      let shouldRemove ← genSmallNat 3
      g := TwoPGraph.apply g (TwoPGraph.addVertex v)
      if shouldRemove == 0 then
        g := TwoPGraph.apply g (TwoPGraph.removeVertex v)
    -- Add edges
    for _ in [0:numEdges] do
      let a ← genSmallNat 10
      let b ← genSmallNat 10
      let shouldRemove ← genSmallNat 3
      g := TwoPGraph.apply g (TwoPGraph.addEdge a b)
      if shouldRemove == 0 then
        g := TwoPGraph.apply g (TwoPGraph.removeEdge a b)
    return g

instance : Arbitrary (TwoPGraphOp Nat) where
  arbitrary := do
    let v ← genSmallNat 10
    let w ← genSmallNat 10
    let opType ← genSmallNat 3
    match opType with
    | 0 => return .addVertex v
    | 1 => return .removeVertex v
    | 2 => return .addEdge v w
    | _ => return .removeEdge v w

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
-- MVRegister Merge Laws (state-level)
#test ∀ (a b : MVRegister Nat), mvRegisterStateEq (MVRegister.merge a b) (MVRegister.merge b a)

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
-- ORSet Merge Laws (state-level)
#test ∀ (a b : ORSet Nat), orsetStateEq (ORSet.merge a b) (ORSet.merge b a)

-- LWWMap Merge Laws
#test ∀ (a b : LWWMap Nat Nat), lwwMapEq (LWWMap.merge a b) (LWWMap.merge b a)
#test ∀ (a b c : LWWMap Nat Nat),
  lwwMapEq (LWWMap.merge (LWWMap.merge a b) c)
           (LWWMap.merge a (LWWMap.merge b c))
#test ∀ (a : LWWMap Nat Nat), lwwMapEq (LWWMap.merge a a) a
-- LWWMap Merge Laws (state-level)
#test ∀ (a b : LWWMap Nat Nat), lwwMapStateEq (LWWMap.merge a b) (LWWMap.merge b a)

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
-- ORMap Merge Laws (state-level)
#test ∀ (a b : ORMap Nat Nat Unit),
  if ormapWellFormed a && ormapWellFormed b && ormapCompatible a b then
    ormapStateEq (ORMap.merge a b) (ORMap.merge b a)
  else
    true

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

-- LSEQ Merge Laws
#test ∀ (a b : LSEQ Nat), lseqEq (LSEQ.merge a b) (LSEQ.merge b a)
#test ∀ (a b c : LSEQ Nat),
  lseqEq (LSEQ.merge (LSEQ.merge a b) c)
         (LSEQ.merge a (LSEQ.merge b c))
#test ∀ (a : LSEQ Nat), lseqEq (LSEQ.merge a a) a

-- Fugue Merge Laws
#test ∀ (a b : Fugue Nat), fugueEq (Fugue.merge a b) (Fugue.merge b a)
#test ∀ (a b c : Fugue Nat),
  fugueEq (Fugue.merge (Fugue.merge a b) c)
          (Fugue.merge a (Fugue.merge b c))
#test ∀ (a : Fugue Nat), fugueEq (Fugue.merge a a) a

-- TwoPGraph Merge Laws
#test ∀ (a b : TwoPGraph Nat), twopgraphEq (TwoPGraph.merge a b) (TwoPGraph.merge b a)
#test ∀ (a b c : TwoPGraph Nat),
  twopgraphEq (TwoPGraph.merge (TwoPGraph.merge a b) c)
              (TwoPGraph.merge a (TwoPGraph.merge b c))
#test ∀ (a : TwoPGraph Nat), twopgraphEq (TwoPGraph.merge a a) a

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
-- MVRegister apply commutes (state-level)
#test ∀ (s : MVRegister Nat) (op1 op2 : MVRegisterOp Nat),
  mvRegisterStateEq (MVRegister.apply (MVRegister.apply s op1) op2)
                    (MVRegister.apply (MVRegister.apply s op2) op1)

-- ORSet apply commutes
#test ∀ (s : ORSet Nat) (op1 op2 : ORSetOp Nat),
  orsetEq (ORSet.apply (ORSet.apply s op1) op2)
          (ORSet.apply (ORSet.apply s op2) op1)
-- ORSet apply commutes (state-level)
#test ∀ (s : ORSet Nat) (op1 op2 : ORSetOp Nat),
  orsetStateEq (ORSet.apply (ORSet.apply s op1) op2)
               (ORSet.apply (ORSet.apply s op2) op1)

-- LWWMap apply commutes
#test ∀ (s : LWWMap Nat Nat) (op1 op2 : LWWMapOp Nat Nat),
  lwwMapEq (LWWMap.apply (LWWMap.apply s op1) op2)
           (LWWMap.apply (LWWMap.apply s op2) op1)
-- LWWMap apply commutes (state-level)
#test ∀ (s : LWWMap Nat Nat) (op1 op2 : LWWMapOp Nat Nat),
  lwwMapStateEq (LWWMap.apply (LWWMap.apply s op1) op2)
                (LWWMap.apply (LWWMap.apply s op2) op1)

-- RGA apply commutes
#test ∀ (s : RGA Nat) (op1 op2 : RGAOp Nat),
  rgaEq (RGA.apply (RGA.apply s op1) op2)
        (RGA.apply (RGA.apply s op2) op1)

-- ORMap apply commutes
#test ∀ (s : ORMap Nat Nat Unit) (op1 op2 : ORMapOp Nat Nat Unit),
  ormapEq (ORMap.apply (ORMap.apply s op1) op2)
          (ORMap.apply (ORMap.apply s op2) op1)
-- ORMap apply commutes (state-level)
#test ∀ (s : ORMap Nat Nat Unit) (op1 op2 : ORMapOp Nat Nat Unit),
  if ormapWellFormed s
      && ormapOpsCompatible op1 op2
      && ormapOpCompatibleWithState s op1
      && ormapOpCompatibleWithState s op2 then
    ormapStateEq (ORMap.apply (ORMap.apply s op1) op2)
                 (ORMap.apply (ORMap.apply s op2) op1)
  else
    true

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

-- LSEQ apply commutes
#test ∀ (s : LSEQ Nat) (op1 op2 : LSEQOp Nat),
  lseqEq (LSEQ.apply (LSEQ.apply s op1) op2)
         (LSEQ.apply (LSEQ.apply s op2) op1)

-- Fugue apply commutes
#test ∀ (s : Fugue Nat) (op1 op2 : FugueOp Nat),
  if fugueOpsCompatible op1 op2
      && fugueOpCompatibleWithState s op1
      && fugueOpCompatibleWithState s op2 then
    fugueEq (Fugue.apply (Fugue.apply s op1) op2)
            (Fugue.apply (Fugue.apply s op2) op1)
  else
    true

-- TwoPGraph apply commutes
#test ∀ (s : TwoPGraph Nat) (op1 op2 : TwoPGraphOp Nat),
  twopgraphEq (TwoPGraph.apply (TwoPGraph.apply s op1) op2)
              (TwoPGraph.apply (TwoPGraph.apply s op2) op1)

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
#test ∀ (f : EWFlag) (ts : LamportTs),
  let f' := EWFlag.apply f (EWFlag.enable ts)
  ewflagEq (EWFlag.apply f' (EWFlag.enable ts)) f'

-- EWFlag disable is idempotent
#test ∀ (f : EWFlag) (ts : LamportTs),
  let f' := EWFlag.apply f (EWFlag.disable ts)
  ewflagEq (EWFlag.apply f' (EWFlag.disable ts)) f'

-- DWFlag enable is idempotent
#test ∀ (f : DWFlag) (ts : LamportTs),
  let f' := DWFlag.apply f (DWFlag.enable ts)
  dwflagEq (DWFlag.apply f' (DWFlag.enable ts)) f'

-- DWFlag disable is idempotent
#test ∀ (f : DWFlag) (ts : LamportTs),
  let f' := DWFlag.apply f (DWFlag.disable ts)
  dwflagEq (DWFlag.apply f' (DWFlag.disable ts)) f'

-- LWWElementSet add is idempotent
#test ∀ (s : LWWElementSet Nat) (v : Nat) (ts : LamportTs),
  let s' := LWWElementSet.apply s (LWWElementSet.add v ts)
  lwwElementSetEq (LWWElementSet.apply s' (LWWElementSet.add v ts)) s'

-- LWWElementSet remove is idempotent
#test ∀ (s : LWWElementSet Nat) (v : Nat) (ts : LamportTs),
  let s' := LWWElementSet.apply s (LWWElementSet.remove v ts)
  lwwElementSetEq (LWWElementSet.apply s' (LWWElementSet.remove v ts)) s'

-- LSEQ insert is idempotent
#test ∀ (lseq : LSEQ Nat) (id : LSEQId) (v : Nat),
  let lseq' := LSEQ.apply lseq (LSEQ.insert id v)
  lseqEq (LSEQ.apply lseq' (LSEQ.insert id v)) lseq'

-- LSEQ delete is idempotent
#test ∀ (lseq : LSEQ Nat) (id : LSEQId),
  let lseq' := LSEQ.apply lseq (LSEQ.delete id)
  lseqEq (LSEQ.apply lseq' (LSEQ.delete id)) lseq'

-- Fugue insert is idempotent
#test ∀ (fugue : Fugue Nat) (node : FugueNode Nat),
  let fugue' := Fugue.apply fugue (Fugue.insert node)
  fugueEq (Fugue.apply fugue' (Fugue.insert node)) fugue'

-- Fugue delete is idempotent
#test ∀ (fugue : Fugue Nat) (id : FugueId),
  let fugue' := Fugue.apply fugue (Fugue.delete id)
  fugueEq (Fugue.apply fugue' (Fugue.delete id)) fugue'

-- TwoPGraph addVertex is idempotent
#test ∀ (g : TwoPGraph Nat) (v : Nat),
  let g' := TwoPGraph.apply g (TwoPGraph.addVertex v)
  twopgraphEq (TwoPGraph.apply g' (TwoPGraph.addVertex v)) g'

-- TwoPGraph removeVertex is idempotent
#test ∀ (g : TwoPGraph Nat) (v : Nat),
  let g' := TwoPGraph.apply g (TwoPGraph.removeVertex v)
  twopgraphEq (TwoPGraph.apply g' (TwoPGraph.removeVertex v)) g'

-- TwoPGraph addEdge is idempotent
#test ∀ (g : TwoPGraph Nat) (a b : Nat),
  let g' := TwoPGraph.apply g (TwoPGraph.addEdge a b)
  twopgraphEq (TwoPGraph.apply g' (TwoPGraph.addEdge a b)) g'

-- TwoPGraph removeEdge is idempotent
#test ∀ (g : TwoPGraph Nat) (a b : Nat),
  let g' := TwoPGraph.apply g (TwoPGraph.removeEdge a b)
  twopgraphEq (TwoPGraph.apply g' (TwoPGraph.removeEdge a b)) g'

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
  let ts := LamportTs.new 1 r
  let f := EWFlag.apply EWFlag.empty (EWFlag.enable ts)
  f.value == true

-- EWFlag: enable-wins for concurrent ops (same time)
#test ∀ (r1 r2 : ReplicaId),
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2
  let f := EWFlag.empty
    |> fun s => EWFlag.apply s (EWFlag.enable tsEnable)
    |> fun s => EWFlag.apply s (EWFlag.disable tsDisable)
  f.value == true

-- DWFlag: empty is false
#test DWFlag.empty.value == false

-- DWFlag: enable makes true (when no disables)
#test ∀ (r : ReplicaId),
  let ts := LamportTs.new 1 r
  let f := DWFlag.apply DWFlag.empty (DWFlag.enable ts)
  f.value == true

-- DWFlag: disable-wins (enable + disable = false)
#test ∀ (r1 r2 : ReplicaId),
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2
  let f := DWFlag.empty
    |> fun s => DWFlag.apply s (DWFlag.enable tsEnable)
    |> fun s => DWFlag.apply s (DWFlag.disable tsDisable)
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

-- LSEQ: contains ID after insert
#test ∀ (id : LSEQId) (v : Nat),
  let lseq := LSEQ.apply LSEQ.empty (LSEQ.insert id v)
  lseq.containsId id

-- LSEQ: delete makes element invisible but keeps ID
#test ∀ (id : LSEQId) (v : Nat),
  let lseq := LSEQ.apply LSEQ.empty (LSEQ.insert id v)
  let lseq' := LSEQ.apply lseq (LSEQ.delete id)
  lseq'.containsId id && lseq'.length == 0

-- LSEQ: insert ordering preserved (lower pos ID comes first)
#test ∀ (v1 v2 : Nat),
  let r : ReplicaId := { id := 1 }
  let id1 := LSEQId.single 5 r
  let id2 := LSEQId.single 10 r
  let lseq := LSEQ.apply LSEQ.empty (LSEQ.insert id2 v2)
  let lseq' := LSEQ.apply lseq (LSEQ.insert id1 v1)
  lseq'.toList == [v1, v2]

-- Fugue: contains ID after insert
#test ∀ (id : FugueId) (v : Nat),
  let node : FugueNode Nat := {
    id := id
    value := some v
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let fugue := Fugue.apply Fugue.empty (Fugue.insert node)
  fugue.containsId id

-- Fugue: delete makes element invisible but keeps ID
#test ∀ (id : FugueId) (v : Nat),
  let node : FugueNode Nat := {
    id := id
    value := some v
    parent := none
    side := .right
    leftOrigin := none
    rightOrigin := none
  }
  let fugue := Fugue.apply Fugue.empty (Fugue.insert node)
  let fugue' := Fugue.apply fugue (Fugue.delete id)
  fugue'.containsId id && fugue'.length == 0

-- TwoPGraph: contains vertex after add
#test ∀ (v : Nat),
  let g := TwoPGraph.apply TwoPGraph.empty (TwoPGraph.addVertex v)
  g.containsVertex v

-- TwoPGraph: vertex removed after remove
#test ∀ (v : Nat),
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex v)
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeVertex v)
  !g.containsVertex v && g.isVertexRemoved v

-- TwoPGraph: once vertex removed, cannot re-add
#test ∀ (v : Nat),
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex v)
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeVertex v)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex v)
  !g.containsVertex v

-- TwoPGraph: contains edge after add (when both endpoints exist)
#test ∀ (a b : Nat),
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex a)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge a b)
  g.containsEdge a b

-- TwoPGraph: edge removed after remove
#test ∀ (a b : Nat),
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex a)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge a b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeEdge a b)
  !g.containsEdge a b && g.isEdgeRemoved a b

-- TwoPGraph: once edge removed, cannot re-add
#test ∀ (a b : Nat),
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex a)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge a b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeEdge a b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge a b)
  !g.containsEdge a b

-- TwoPGraph: vertex removal hides edges
#test ∀ (a b : Nat),
  let g := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex a)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge a b)
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeVertex a)
  !g.containsEdge a b

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

-- LSEQ convergence (3 ops)
#test ∀ (lseq : LSEQ Nat) (op1 op2 op3 : LSEQOp Nat),
  let forward := LSEQ.apply (LSEQ.apply (LSEQ.apply lseq op1) op2) op3
  let reverse := LSEQ.apply (LSEQ.apply (LSEQ.apply lseq op3) op2) op1
  lseqEq forward reverse

-- Fugue convergence (3 ops)
#test ∀ (fugue : Fugue Nat) (op1 op2 op3 : FugueOp Nat),
  if fugueOpsCompatible op1 op2
      && fugueOpsCompatible op1 op3
      && fugueOpsCompatible op2 op3
      && fugueOpCompatibleWithState fugue op1
      && fugueOpCompatibleWithState fugue op2
      && fugueOpCompatibleWithState fugue op3 then
    let forward := Fugue.apply (Fugue.apply (Fugue.apply fugue op1) op2) op3
    let reverse := Fugue.apply (Fugue.apply (Fugue.apply fugue op3) op2) op1
    fugueEq forward reverse
  else
    true

-- TwoPGraph convergence (3 ops)
#test ∀ (g : TwoPGraph Nat) (op1 op2 op3 : TwoPGraphOp Nat),
  let forward := TwoPGraph.apply (TwoPGraph.apply (TwoPGraph.apply g op1) op2) op3
  let reverse := TwoPGraph.apply (TwoPGraph.apply (TwoPGraph.apply g op3) op2) op1
  twopgraphEq forward reverse

end ConvergentTests.PropertyTests
