import Convergent
import Crucible

namespace ConvergentTests.RegisterTests

open Crucible
open Convergent

testSuite "LWWRegister"

test "LWWReg empty returns none" := do
  let reg : LWWRegister String := LWWRegister.empty
  (reg.get) ≡ (none : Option String)

test "LWWReg set updates value" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  let reg := runCRDT LWWRegister.empty do
    LWWRegister.setM "hello" ts
  (reg.get) ≡ some "hello"

test "LWWReg later timestamp wins" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let reg := runCRDT LWWRegister.empty do
    LWWRegister.setM "first" ts1
    LWWRegister.setM "second" ts2
  (reg.get) ≡ some "second"

test "LWWReg earlier timestamp ignored" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let reg := runCRDT LWWRegister.empty do
    LWWRegister.setM "second" ts2
    LWWRegister.setM "first" ts1
  (reg.get) ≡ some "second"

test "LWWReg replica id breaks ties" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 5 r1
  let ts2 := LamportTs.new 5 r2
  let reg := runCRDT LWWRegister.empty do
    LWWRegister.setM "from r1" ts1
    LWWRegister.setM "from r2" ts2
  (reg.get) ≡ some "from r2"

testSuite "MVRegister"

test "MVReg empty returns empty" := do
  let reg : MVRegister String := MVRegister.empty
  (reg.get) ≡ ([] : List String)

test "MVReg single set returns value" := do
  let r1 : ReplicaId := 1
  let vc := VectorClock.empty.inc r1
  let reg := runCRDT MVRegister.empty do
    MVRegister.setM "hello" vc
  (reg.get) ≡ ["hello"]

test "MVReg concurrent writes multiple values" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let vc1 := VectorClock.empty.inc r1
  let vc2 := VectorClock.empty.inc r2
  let reg := runCRDT MVRegister.empty do
    MVRegister.setM "from r1" vc1
    MVRegister.setM "from r2" vc2
  (reg.get.length) ≡ 2

test "MVReg later write dominates" := do
  let r1 : ReplicaId := 1
  let vc1 := VectorClock.empty.inc r1
  let vc2 := vc1.inc r1
  let reg := runCRDT MVRegister.empty do
    MVRegister.setM "first" vc1
    MVRegister.setM "second" vc2
  (reg.get) ≡ ["second"]

test "MVReg equivalent clocks choose stable winner" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Same logical clock, different construction order
  let vc12 := VectorClock.empty.inc r1 |>.inc r2
  let vc21 := VectorClock.empty.inc r2 |>.inc r1
  let regA := MVRegister.apply MVRegister.empty (MVRegister.set "z" vc12)
  let regB := MVRegister.apply MVRegister.empty (MVRegister.set "a" vc21)
  let merged1 := MVRegister.merge regA regB
  let merged2 := MVRegister.merge regB regA
  (merged1.get) ≡ (merged2.get)
  -- Expect deterministic tie-breaker for equivalent clocks
  (merged1.get) ≡ ["z"]

end ConvergentTests.RegisterTests
