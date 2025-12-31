import Convergent
import Crucible

namespace ConvergentTests.FlagTests

open Crucible
open Convergent

testSuite "EWFlag"

test "EWFlag empty is false" := do
  let f := EWFlag.empty
  (f.value) ≡ false

test "EWFlag enable makes true" := do
  let r1 : ReplicaId := 1
  let f := EWFlag.apply EWFlag.empty (EWFlag.enable r1)
  (f.value) ≡ true

test "EWFlag disable after enable stays true (enable-wins)" := do
  let r1 : ReplicaId := 1
  let f := EWFlag.empty
    |> fun s => EWFlag.apply s (EWFlag.enable r1)
    |> fun s => EWFlag.apply s (EWFlag.disable r1)
  (f.value) ≡ true

test "EWFlag enable after disable is true" := do
  let r1 : ReplicaId := 1
  let f := EWFlag.empty
    |> fun s => EWFlag.apply s (EWFlag.disable r1)
    |> fun s => EWFlag.apply s (EWFlag.enable r1)
  (f.value) ≡ true

test "EWFlag concurrent enable + disable is true" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Simulate concurrent: r1 enables, r2 disables
  let f := EWFlag.empty
    |> fun s => EWFlag.apply s (EWFlag.enable r1)
    |> fun s => EWFlag.apply s (EWFlag.disable r2)
  (f.value) ≡ true

test "EWFlag merge preserves enable-wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- f1: enabled by r1
  let f1 := EWFlag.apply EWFlag.empty (EWFlag.enable r1)
  -- f2: disabled by r2
  let f2 := EWFlag.apply EWFlag.empty (EWFlag.disable r2)
  -- Merged: should be true (enable-wins)
  let merged := EWFlag.merge f1 f2
  (merged.value) ≡ true

test "EWFlag multiple enables" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let f := EWFlag.empty
    |> fun s => EWFlag.apply s (EWFlag.enable r1)
    |> fun s => EWFlag.apply s (EWFlag.enable r2)
  (f.value) ≡ true

testSuite "DWFlag"

test "DWFlag empty is false" := do
  let f := DWFlag.empty
  (f.value) ≡ false

test "DWFlag enable makes true" := do
  let r1 : ReplicaId := 1
  let f := DWFlag.apply DWFlag.empty (DWFlag.enable r1)
  (f.value) ≡ true

test "DWFlag disable after enable makes false (disable-wins)" := do
  let r1 : ReplicaId := 1
  let f := DWFlag.empty
    |> fun s => DWFlag.apply s (DWFlag.enable r1)
    |> fun s => DWFlag.apply s (DWFlag.disable r1)
  (f.value) ≡ false

test "DWFlag enable after disable stays false" := do
  let r1 : ReplicaId := 1
  let f := DWFlag.empty
    |> fun s => DWFlag.apply s (DWFlag.disable r1)
    |> fun s => DWFlag.apply s (DWFlag.enable r1)
  (f.value) ≡ false

test "DWFlag concurrent enable + disable is false" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Simulate concurrent: r1 enables, r2 disables
  let f := DWFlag.empty
    |> fun s => DWFlag.apply s (DWFlag.enable r1)
    |> fun s => DWFlag.apply s (DWFlag.disable r2)
  (f.value) ≡ false

test "DWFlag merge preserves disable-wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- f1: enabled by r1
  let f1 := DWFlag.apply DWFlag.empty (DWFlag.enable r1)
  -- f2: disabled by r2
  let f2 := DWFlag.apply DWFlag.empty (DWFlag.disable r2)
  -- Merged: should be false (disable-wins)
  let merged := DWFlag.merge f1 f2
  (merged.value) ≡ false

test "DWFlag only enable no disable is true" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let f := DWFlag.empty
    |> fun s => DWFlag.apply s (DWFlag.enable r1)
    |> fun s => DWFlag.apply s (DWFlag.enable r2)
  (f.value) ≡ true

test "DWFlag disable without enable is false" := do
  let r1 : ReplicaId := 1
  let f := DWFlag.apply DWFlag.empty (DWFlag.disable r1)
  (f.value) ≡ false

#generate_tests

end ConvergentTests.FlagTests
