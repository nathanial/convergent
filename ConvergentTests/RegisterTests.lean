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
  let reg := LWWRegister.apply LWWRegister.empty (LWWRegister.set "hello" ts)
  (reg.get) ≡ some "hello"

test "LWWReg later timestamp wins" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let reg := LWWRegister.empty
    |> fun s => LWWRegister.apply s (LWWRegister.set "first" ts1)
    |> fun s => LWWRegister.apply s (LWWRegister.set "second" ts2)
  (reg.get) ≡ some "second"

test "LWWReg earlier timestamp ignored" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let reg := LWWRegister.empty
    |> fun s => LWWRegister.apply s (LWWRegister.set "second" ts2)
    |> fun s => LWWRegister.apply s (LWWRegister.set "first" ts1)
  (reg.get) ≡ some "second"

test "LWWReg replica id breaks ties" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 5 r1
  let ts2 := LamportTs.new 5 r2
  let reg := LWWRegister.empty
    |> fun s => LWWRegister.apply s (LWWRegister.set "from r1" ts1)
    |> fun s => LWWRegister.apply s (LWWRegister.set "from r2" ts2)
  (reg.get) ≡ some "from r2"

testSuite "MVRegister"

test "MVReg empty returns empty" := do
  let reg : MVRegister String := MVRegister.empty
  (reg.get) ≡ ([] : List String)

test "MVReg single set returns value" := do
  let r1 : ReplicaId := 1
  let vc := VectorClock.empty.inc r1
  let reg := MVRegister.apply MVRegister.empty (MVRegister.set "hello" vc)
  (reg.get) ≡ ["hello"]

test "MVReg concurrent writes multiple values" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let vc1 := VectorClock.empty.inc r1
  let vc2 := VectorClock.empty.inc r2
  let reg := MVRegister.empty
    |> fun s => MVRegister.apply s (MVRegister.set "from r1" vc1)
    |> fun s => MVRegister.apply s (MVRegister.set "from r2" vc2)
  (reg.get.length) ≡ 2

test "MVReg later write dominates" := do
  let r1 : ReplicaId := 1
  let vc1 := VectorClock.empty.inc r1
  let vc2 := vc1.inc r1
  let reg := MVRegister.empty
    |> fun s => MVRegister.apply s (MVRegister.set "first" vc1)
    |> fun s => MVRegister.apply s (MVRegister.set "second" vc2)
  (reg.get) ≡ ["second"]

#generate_tests

end ConvergentTests.RegisterTests
