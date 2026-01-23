import Convergent
import Crucible

namespace ConvergentTests.GraphTests

open Crucible
open Convergent

testSuite "TwoPGraph"

test "TwoPGraph empty has no vertices" := do
  let g : TwoPGraph Nat := TwoPGraph.empty
  (g.vertexCount) ≡ 0
  (g.edgeCount) ≡ 0

test "TwoPGraph add vertex" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
  (g.containsVertex 1) ≡ true
  (g.vertexCount) ≡ 1

test "TwoPGraph add multiple vertices" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addVertexM 3
  (g.vertexCount) ≡ 3
  (g.containsVertex 1) ≡ true
  (g.containsVertex 2) ≡ true
  (g.containsVertex 3) ≡ true

test "TwoPGraph remove vertex" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.removeVertexM 1
  (g.containsVertex 1) ≡ false
  (g.isVertexRemoved 1) ≡ true

test "TwoPGraph cannot re-add removed vertex" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.removeVertexM 1
    TwoPGraph.addVertexM 1
  (g.containsVertex 1) ≡ false

test "TwoPGraph add edge" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addEdgeM 1 2
  (g.containsEdge 1 2) ≡ true
  (g.edgeCount) ≡ 1

test "TwoPGraph edge requires both endpoints" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addEdgeM 1 2  -- vertex 2 not added
  (g.containsEdge 1 2) ≡ false  -- edge not "present" since 2 is not a vertex

test "TwoPGraph remove edge" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addEdgeM 1 2
    TwoPGraph.removeEdgeM 1 2
  (g.containsEdge 1 2) ≡ false
  (g.isEdgeRemoved 1 2) ≡ true

test "TwoPGraph cannot re-add removed edge" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addEdgeM 1 2
    TwoPGraph.removeEdgeM 1 2
    TwoPGraph.addEdgeM 1 2
  (g.containsEdge 1 2) ≡ false

test "TwoPGraph vertex removal hides edges" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addEdgeM 1 2
    TwoPGraph.removeVertexM 1
  -- Edge still exists in edge set but is not "present" since vertex 1 is gone
  (g.containsEdge 1 2) ≡ false
  (g.edgeCount) ≡ 0

test "TwoPGraph neighbors" := do
  let g := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addVertexM 3
    TwoPGraph.addEdgeM 1 2
    TwoPGraph.addEdgeM 1 3
  let neighbors := g.neighbors 1
  (neighbors.length) ≡ 2
  (neighbors.any (· == 2)) ≡ true
  (neighbors.any (· == 3)) ≡ true
  (g.predecessors 2) ≡ [1]

test "TwoPGraph merge combines vertices and edges" := do
  let g1 := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.addVertexM 2
    TwoPGraph.addEdgeM 1 2
  let g2 := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 2
    TwoPGraph.addVertexM 3
    TwoPGraph.addEdgeM 2 3
  let merged := TwoPGraph.merge g1 g2
  (merged.vertexCount) ≡ 3
  (merged.containsEdge 1 2) ≡ true
  (merged.containsEdge 2 3) ≡ true

test "TwoPGraph merge remove wins" := do
  let g1 := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
  let g2 := runCRDT (TwoPGraph.empty : TwoPGraph Nat) do
    TwoPGraph.addVertexM 1
    TwoPGraph.removeVertexM 1
  let merged := TwoPGraph.merge g1 g2
  (merged.containsVertex 1) ≡ false

end ConvergentTests.GraphTests
