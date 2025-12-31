import Convergent
import Crucible

namespace ConvergentTests.MapTests

open Crucible
open Convergent

testSuite "LWWMap"

test "LWWMap empty returns none" := do
  let m : LWWMap String Nat := LWWMap.empty
  (m.get "key") ≡ (none : Option Nat)

test "LWWMap put adds value" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  let m := LWWMap.apply LWWMap.empty (LWWMap.put "key" 42 ts)
  (m.get "key") ≡ some 42

test "LWWMap later put wins" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "key" 1 ts1)
    |> fun s => LWWMap.apply s (LWWMap.put "key" 2 ts2)
  (m.get "key") ≡ some 2

test "LWWMap delete removes key" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "key" 42 ts1)
    |> fun s => LWWMap.apply s (LWWMap.delete "key" ts2)
  (m.get "key") ≡ (none : Option Nat)
  (m.contains "key") ≡ false

test "LWWMap put after delete" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r1
  let ts3 := LamportTs.new 3 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "key" 42 ts1)
    |> fun s => LWWMap.apply s (LWWMap.delete "key" ts2)
    |> fun s => LWWMap.apply s (LWWMap.put "key" 100 ts3)
  (m.get "key") ≡ some 100

test "LWWMap multiple keys" := do
  let r1 : ReplicaId := 1
  let ts := LamportTs.new 1 r1
  let m := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "a" 1 ts)
    |> fun s => LWWMap.apply s (LWWMap.put "b" 2 ts)
    |> fun s => LWWMap.apply s (LWWMap.put "c" 3 ts)
  (m.size) ≡ 3
  (m.get "a") ≡ some 1
  (m.get "b") ≡ some 2
  (m.get "c") ≡ some 3

#generate_tests

end ConvergentTests.MapTests
