/-
  Binary Serialization for Graph CRDTs

  Provides BinarySerialize instances for:
  - TwoPGraph, TwoPGraphOp
-/
import Convergent.Serialization.Set
import Convergent.Graph.TwoPGraph

namespace Convergent.Serialization

open Convergent

/-! ## TwoPGraph -/

instance [BEq V] [Hashable V] [BinarySerialize V] : BinarySerialize (TwoPGraph V) where
  encode g :=
    BinarySerialize.encode g.vertices ++ BinarySerialize.encode g.edges
  decode bytes offset := do
    let (vertices, offset') ← BinarySerialize.decode bytes offset
    let (edges, consumed) ← BinarySerialize.decode bytes offset'
    return ({ vertices, edges }, consumed)

instance [BinarySerialize V] : BinarySerialize (TwoPGraphOp V) where
  encode op := match op with
    | .addVertex v =>
      ByteArray.mk #[0] ++ BinarySerialize.encode v
    | .removeVertex v =>
      ByteArray.mk #[1] ++ BinarySerialize.encode v
    | .addEdge from_ to =>
      ByteArray.mk #[2] ++ BinarySerialize.encode from_ ++ BinarySerialize.encode to
    | .removeEdge from_ to =>
      ByteArray.mk #[3] ++ BinarySerialize.encode from_ ++ BinarySerialize.encode to
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (v, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.addVertex v, consumed)
    | 1 =>
      let (v, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.removeVertex v, consumed)
    | 2 =>
      let (from_, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (to, consumed) ← BinarySerialize.decode bytes offset'
      return (.addEdge from_ to, consumed)
    | 3 =>
      let (from_, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (to, consumed) ← BinarySerialize.decode bytes offset'
      return (.removeEdge from_ to, consumed)
    | _ => none

end Convergent.Serialization
