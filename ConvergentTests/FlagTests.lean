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
  let ts1 := LamportTs.new 1 r1
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM ts1
  (f.value) ≡ true

test "EWFlag disable after enable makes false (later disable)" := do
  let r1 : ReplicaId := 1
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 2 r1
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM tsEnable
    EWFlag.disableM tsDisable
  (f.value) ≡ false

test "EWFlag enable after disable is true (later enable)" := do
  let r1 : ReplicaId := 1
  let tsDisable := LamportTs.new 1 r1
  let tsEnable := LamportTs.new 2 r1
  let f := runCRDT EWFlag.empty do
    EWFlag.disableM tsDisable
    EWFlag.enableM tsEnable
  (f.value) ≡ true

test "EWFlag concurrent enable + disable is true" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2
  -- Simulate concurrent: r1 enables, r2 disables
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM tsEnable
    EWFlag.disableM tsDisable
  (f.value) ≡ true

test "EWFlag merge preserves enable-wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2
  -- f1: enabled by r1
  let f1 := runCRDT EWFlag.empty do
    EWFlag.enableM tsEnable
  -- f2: disabled by r2
  let f2 := runCRDT EWFlag.empty do
    EWFlag.disableM tsDisable
  -- Merged: should be true (enable-wins)
  let merged := EWFlag.merge f1 f2
  (merged.value) ≡ true

test "EWFlag multiple enables" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r2
  let f := runCRDT EWFlag.empty do
    EWFlag.enableM ts1
    EWFlag.enableM ts2
  (f.value) ≡ true

testSuite "DWFlag"

test "DWFlag empty is false" := do
  let f := DWFlag.empty
  (f.value) ≡ false

test "DWFlag enable makes true" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM ts1
  (f.value) ≡ true

test "DWFlag disable after enable makes false (disable-wins)" := do
  let r1 : ReplicaId := 1
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 2 r1
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM tsEnable
    DWFlag.disableM tsDisable
  (f.value) ≡ false

test "DWFlag enable after disable is true (later enable)" := do
  let r1 : ReplicaId := 1
  let tsDisable := LamportTs.new 1 r1
  let tsEnable := LamportTs.new 2 r1
  let f := runCRDT DWFlag.empty do
    DWFlag.disableM tsDisable
    DWFlag.enableM tsEnable
  (f.value) ≡ true

test "DWFlag concurrent enable + disable is false" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2
  -- Simulate concurrent: r1 enables, r2 disables
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM tsEnable
    DWFlag.disableM tsDisable
  (f.value) ≡ false

test "DWFlag merge preserves disable-wins" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let tsEnable := LamportTs.new 1 r1
  let tsDisable := LamportTs.new 1 r2
  -- f1: enabled by r1
  let f1 := runCRDT DWFlag.empty do
    DWFlag.enableM tsEnable
  -- f2: disabled by r2
  let f2 := runCRDT DWFlag.empty do
    DWFlag.disableM tsDisable
  -- Merged: should be false (disable-wins)
  let merged := DWFlag.merge f1 f2
  (merged.value) ≡ false

test "DWFlag only enable no disable is true" := do
  let r1 : ReplicaId := 1
  let r2 : ReplicaId := 2
  let ts1 := LamportTs.new 1 r1
  let ts2 := LamportTs.new 2 r2
  let f := runCRDT DWFlag.empty do
    DWFlag.enableM ts1
    DWFlag.enableM ts2
  (f.value) ≡ true

test "DWFlag disable without enable is false" := do
  let r1 : ReplicaId := 1
  let ts1 := LamportTs.new 1 r1
  let f := runCRDT DWFlag.empty do
    DWFlag.disableM ts1
  (f.value) ≡ false

end ConvergentTests.FlagTests
