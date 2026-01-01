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
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM r1
  (f.value) ≡ true

test "EWFlag disable after enable stays true (enable-wins)" := do
  let r1 : ReplicaId := 1
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM r1
    EWFlag.disableM r1
  (f.value) ≡ true

test "EWFlag enable after disable is true" := do
  let r1 : ReplicaId := 1
  let f := runCRDT EWFlag.empty do
    EWFlag.disableM r1
    EWFlag.enableM r1
  (f.value) ≡ true

test "EWFlag concurrent enable + disable is true" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Simulate concurrent: r1 enables, r2 disables
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM r1
    EWFlag.disableM r2
  (f.value) ≡ true

test "EWFlag merge preserves enable-wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- f1: enabled by r1
  let f1 := runCRDT EWFlag.empty do
    EWFlag.enableM r1
  -- f2: disabled by r2
  let f2 := runCRDT EWFlag.empty do
    EWFlag.disableM r2
  -- Merged: should be true (enable-wins)
  let merged := EWFlag.merge f1 f2
  (merged.value) ≡ true

test "EWFlag multiple enables" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM r1
    EWFlag.enableM r2
  (f.value) ≡ true

testSuite "DWFlag"

test "DWFlag empty is false" := do
  let f := DWFlag.empty
  (f.value) ≡ false

test "DWFlag enable makes true" := do
  let r1 : ReplicaId := 1
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM r1
  (f.value) ≡ true

test "DWFlag disable after enable makes false (disable-wins)" := do
  let r1 : ReplicaId := 1
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM r1
    DWFlag.disableM r1
  (f.value) ≡ false

test "DWFlag enable after disable stays false" := do
  let r1 : ReplicaId := 1
  let f := runCRDT DWFlag.empty do
    DWFlag.disableM r1
    DWFlag.enableM r1
  (f.value) ≡ false

test "DWFlag concurrent enable + disable is false" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- Simulate concurrent: r1 enables, r2 disables
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM r1
    DWFlag.disableM r2
  (f.value) ≡ false

test "DWFlag merge preserves disable-wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  -- f1: enabled by r1
  let f1 := runCRDT DWFlag.empty do
    DWFlag.enableM r1
  -- f2: disabled by r2
  let f2 := runCRDT DWFlag.empty do
    DWFlag.disableM r2
  -- Merged: should be false (disable-wins)
  let merged := DWFlag.merge f1 f2
  (merged.value) ≡ false

test "DWFlag only enable no disable is true" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM r1
    DWFlag.enableM r2
  (f.value) ≡ true

test "DWFlag disable without enable is false" := do
  let r1 : ReplicaId := 1
  let f := runCRDT DWFlag.empty do
    DWFlag.disableM r1
  (f.value) ≡ false

#generate_tests

end ConvergentTests.FlagTests
