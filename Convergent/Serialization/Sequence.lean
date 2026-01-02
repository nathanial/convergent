/-
  Binary Serialization for Sequence CRDTs

  Provides BinarySerialize instances for:
  - RGA, RGAOp, RGANode
  - LSEQ, LSEQOp, LSEQNode, LSEQId, LSEQLevel, LSEQStrategy
  - Fugue, FugueOp, FugueNode, FugueId, FugueSide
-/
import Convergent.Serialization.Core
import Convergent.Sequence.RGA
import Convergent.Sequence.LSEQ
import Convergent.Sequence.Fugue

namespace Convergent.Serialization

open Convergent

/-! ## RGA -/

instance [BinarySerialize α] : BinarySerialize (RGANode α) where
  encode node :=
    BinarySerialize.encode node.id ++
    BinarySerialize.encode node.afterId ++
    BinarySerialize.encode node.value
  decode bytes offset := do
    let (id, offset') ← BinarySerialize.decode bytes offset
    let (afterId, offset'') ← BinarySerialize.decode bytes offset'
    let (value, consumed) ← BinarySerialize.decode bytes offset''
    return ({ id, afterId, value }, consumed)

instance [BinarySerialize α] : BinarySerialize (RGA α) where
  encode rga := BinarySerialize.encode rga.nodes
  decode bytes offset := do
    let (nodes, consumed) ← BinarySerialize.decode bytes offset
    return ({ nodes }, consumed)

instance [BinarySerialize α] : BinarySerialize (RGAOp α) where
  encode op := match op with
    | .insert afterId value id =>
      ByteArray.mk #[0] ++ BinarySerialize.encode afterId ++
        BinarySerialize.encode value ++ BinarySerialize.encode id
    | .delete id =>
      ByteArray.mk #[1] ++ BinarySerialize.encode id
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (afterId, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (value, offset'') ← BinarySerialize.decode bytes offset'
      let (id, consumed) ← BinarySerialize.decode bytes offset''
      return (.insert afterId value id, consumed)
    | 1 =>
      let (id, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.delete id, consumed)
    | _ => none

/-! ## LSEQ -/

instance : BinarySerialize LSEQStrategy where
  encode s := match s with
    | .boundaryPlus => ByteArray.mk #[0]
    | .boundaryMinus => ByteArray.mk #[1]
  decode bytes offset := do
    guard (offset < bytes.size)
    match bytes.get! offset with
    | 0 => return (.boundaryPlus, offset + 1)
    | 1 => return (.boundaryMinus, offset + 1)
    | _ => none

instance : BinarySerialize LSEQLevel where
  encode lvl :=
    encodeNat lvl.pos ++ BinarySerialize.encode lvl.site
  decode bytes offset := do
    let (pos, offset') ← decodeNat bytes offset
    let (site, consumed) ← BinarySerialize.decode bytes offset'
    return ({ pos, site }, consumed)

instance : BinarySerialize LSEQId where
  encode id := BinarySerialize.encode id.levels
  decode bytes offset := do
    let (levels, consumed) ← BinarySerialize.decode bytes offset
    return ({ levels }, consumed)

instance [BinarySerialize α] : BinarySerialize (LSEQNode α) where
  encode node :=
    BinarySerialize.encode node.id ++ BinarySerialize.encode node.value
  decode bytes offset := do
    let (id, offset') ← BinarySerialize.decode bytes offset
    let (value, consumed) ← BinarySerialize.decode bytes offset'
    return ({ id, value }, consumed)

instance [BinarySerialize α] : BinarySerialize (LSEQ α) where
  encode lseq := BinarySerialize.encode lseq.nodes
  decode bytes offset := do
    let (nodes, consumed) ← BinarySerialize.decode bytes offset
    return ({ nodes }, consumed)

instance [BinarySerialize α] : BinarySerialize (LSEQOp α) where
  encode op := match op with
    | .insert id value =>
      ByteArray.mk #[0] ++ BinarySerialize.encode id ++ BinarySerialize.encode value
    | .delete id =>
      ByteArray.mk #[1] ++ BinarySerialize.encode id
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (id, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (value, consumed) ← BinarySerialize.decode bytes offset'
      return (.insert id value, consumed)
    | 1 =>
      let (id, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.delete id, consumed)
    | _ => none

/-! ## Fugue -/

instance : BinarySerialize FugueId where
  encode id :=
    BinarySerialize.encode id.replica ++ encodeNat id.counter
  decode bytes offset := do
    let (replica, offset') ← BinarySerialize.decode bytes offset
    let (counter, consumed) ← decodeNat bytes offset'
    return ({ replica, counter }, consumed)

instance : BinarySerialize FugueSide where
  encode s := match s with
    | .left => ByteArray.mk #[0]
    | .right => ByteArray.mk #[1]
  decode bytes offset := do
    guard (offset < bytes.size)
    match bytes.get! offset with
    | 0 => return (.left, offset + 1)
    | 1 => return (.right, offset + 1)
    | _ => none

instance [BinarySerialize α] : BinarySerialize (FugueNode α) where
  encode node :=
    BinarySerialize.encode node.id ++
    BinarySerialize.encode node.value ++
    BinarySerialize.encode node.parent ++
    BinarySerialize.encode node.side ++
    BinarySerialize.encode node.leftOrigin ++
    BinarySerialize.encode node.rightOrigin
  decode bytes offset := do
    let (id, offset') ← BinarySerialize.decode bytes offset
    let (value, offset'') ← BinarySerialize.decode bytes offset'
    let (parent, offset''') ← BinarySerialize.decode bytes offset''
    let (side, offset'''') ← BinarySerialize.decode bytes offset'''
    let (leftOrigin, offset''''') ← BinarySerialize.decode bytes offset''''
    let (rightOrigin, consumed) ← BinarySerialize.decode bytes offset'''''
    return ({ id, value, parent, side, leftOrigin, rightOrigin }, consumed)

instance [BinarySerialize α] : BinarySerialize (Fugue α) where
  encode f := BinarySerialize.encode f.nodes.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ nodes := Std.HashMap.ofList list }, consumed)

instance [BinarySerialize α] : BinarySerialize (FugueOp α) where
  encode op := match op with
    | .insert node =>
      ByteArray.mk #[0] ++ BinarySerialize.encode node
    | .delete id =>
      ByteArray.mk #[1] ++ BinarySerialize.encode id
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (node, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.insert node, consumed)
    | 1 =>
      let (id, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.delete id, consumed)
    | _ => none

end Convergent.Serialization
