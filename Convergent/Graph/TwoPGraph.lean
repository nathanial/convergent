/-
  TwoPGraph - Two-Phase Graph (2P2PGraph)

  A graph CRDT that applies the two-phase set pattern to both vertices
  and edges. Once a vertex or edge is removed, it cannot be re-added.

  This is suitable for graphs where deletions are permanent, such as
  blocking relationships or finalized connections.

  State: Two TwoPSets - one for vertices, one for edges.
  An edge is only "present" if both its endpoints are present vertices.

  Operations:
  - AddVertex: Add a vertex (if not already removed)
  - RemoveVertex: Remove a vertex permanently
  - AddEdge: Add an edge between two vertices
  - RemoveEdge: Remove an edge permanently
-/
import Convergent.Core.CmRDT
import Convergent.Set.TwoPSet

namespace Convergent

/-- Two-phase graph: vertices and edges are both TwoPSets -/
structure TwoPGraph (V : Type) [BEq V] [Hashable V] where
  vertices : TwoPSet V
  edges : TwoPSet (V × V)
  deriving Repr, Inhabited

/-- Operations on a two-phase graph -/
inductive TwoPGraphOp (V : Type) where
  | addVertex (v : V)
  | removeVertex (v : V)
  | addEdge (from_ : V) (to : V)
  | removeEdge (from_ : V) (to : V)
  deriving Repr

namespace TwoPGraph

variable {V : Type} [BEq V] [Hashable V]

/-- Empty graph -/
def empty : TwoPGraph V :=
  { vertices := TwoPSet.empty
  , edges := TwoPSet.empty }

/-- Check if a vertex is present (added and not removed) -/
def containsVertex (g : TwoPGraph V) (v : V) : Bool :=
  g.vertices.contains v

/-- Check if an edge is present (added, not removed, and both endpoints present) -/
def containsEdge (g : TwoPGraph V) (from_ to : V) : Bool :=
  g.edges.contains (from_, to) && g.containsVertex from_ && g.containsVertex to

/-- Get all present vertices -/
def getVertices (g : TwoPGraph V) : List V :=
  g.vertices.toList

/-- Get all present edges (only those with both endpoints present) -/
def getEdges (g : TwoPGraph V) : List (V × V) :=
  g.edges.toList.filter fun (a, b) => g.containsVertex a && g.containsVertex b

/-- Get neighbors of a vertex (outgoing edges) -/
def neighbors (g : TwoPGraph V) (v : V) : List V :=
  g.getEdges.filterMap fun (a, b) => if a == v then some b else none

/-- Get predecessors of a vertex (incoming edges) -/
def predecessors (g : TwoPGraph V) (v : V) : List V :=
  g.getEdges.filterMap fun (a, b) => if b == v then some a else none

/-- Count of present vertices -/
def vertexCount (g : TwoPGraph V) : Nat :=
  g.getVertices.length

/-- Count of present edges -/
def edgeCount (g : TwoPGraph V) : Nat :=
  g.getEdges.length

/-- Check if a vertex has been removed (in tombstone set) -/
def isVertexRemoved (g : TwoPGraph V) (v : V) : Bool :=
  g.vertices.removed.contains v

/-- Check if an edge has been removed (in tombstone set) -/
def isEdgeRemoved (g : TwoPGraph V) (from_ to : V) : Bool :=
  g.edges.removed.contains (from_, to)

/-- Apply an operation to the graph -/
def apply (g : TwoPGraph V) (op : TwoPGraphOp V) : TwoPGraph V :=
  match op with
  | .addVertex v =>
    { g with vertices := TwoPSet.apply g.vertices (TwoPSet.add v) }
  | .removeVertex v =>
    { g with vertices := TwoPSet.apply g.vertices (TwoPSet.remove v) }
  | .addEdge from_ to =>
    { g with edges := TwoPSet.apply g.edges (TwoPSet.add (from_, to)) }
  | .removeEdge from_ to =>
    { g with edges := TwoPSet.apply g.edges (TwoPSet.remove (from_, to)) }

/-- Create an add vertex operation -/
def addVertex (v : V) : TwoPGraphOp V := .addVertex v

/-- Create a remove vertex operation -/
def removeVertex (v : V) : TwoPGraphOp V := .removeVertex v

/-- Create an add edge operation -/
def addEdge (from_ to : V) : TwoPGraphOp V := .addEdge from_ to

/-- Create a remove edge operation -/
def removeEdge (from_ to : V) : TwoPGraphOp V := .removeEdge from_ to

/-- Merge two graphs -/
def merge (a b : TwoPGraph V) : TwoPGraph V :=
  { vertices := TwoPSet.merge a.vertices b.vertices
  , edges := TwoPSet.merge a.edges b.edges }

instance : CmRDT (TwoPGraph V) (TwoPGraphOp V) where
  empty := empty
  apply := apply
  merge := merge

instance : CmRDTQuery (TwoPGraph V) (TwoPGraphOp V) (List V) where
  query := getVertices

instance [ToString V] : ToString (TwoPGraph V) where
  toString g :=
    let vs := g.getVertices.map toString
    let es := g.getEdges.map fun (a, b) => s!"{a} → {b}"
    s!"TwoPGraph(vertices: [{", ".intercalate vs}], edges: [{", ".intercalate es}])"

/-! ## Monadic Interface -/

/-- Add a vertex in the CRDT monad -/
def addVertexM (v : V) : CRDTM (TwoPGraph V) Unit :=
  applyM (addVertex v)

/-- Remove a vertex in the CRDT monad -/
def removeVertexM (v : V) : CRDTM (TwoPGraph V) Unit :=
  applyM (removeVertex v)

/-- Add an edge in the CRDT monad -/
def addEdgeM (from_ to : V) : CRDTM (TwoPGraph V) Unit :=
  applyM (addEdge from_ to)

/-- Remove an edge in the CRDT monad -/
def removeEdgeM (from_ to : V) : CRDTM (TwoPGraph V) Unit :=
  applyM (removeEdge from_ to)

end TwoPGraph

end Convergent
