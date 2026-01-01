/-
  Binary Serialization for Set CRDTs

  Provides BinarySerialize instances for:
  - GSet, GSetOp
  - TwoPSet, TwoPSetOp
  - ORSet, ORSetOp
  - LWWElementSet, LWWElementSetOp
-/
import Convergent.Serialization.Core
import Convergent.Set.GSet
import Convergent.Set.TwoPSet
import Convergent.Set.ORSet
import Convergent.Set.LWWElementSet

namespace Convergent.Serialization

open Convergent

/-! ## GSet -/

instance [BEq α] [Hashable α] [BinarySerialize α] : BinarySerialize (GSet α) where
  encode gs := BinarySerialize.encode gs.elements.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ elements := Std.HashSet.ofList list }, consumed)

instance [BinarySerialize α] : BinarySerialize (GSetOp α) where
  encode op := BinarySerialize.encode op.value
  decode bytes offset := do
    let (value, consumed) ← BinarySerialize.decode bytes offset
    return ({ value }, consumed)

/-! ## TwoPSet -/

instance [BEq α] [Hashable α] [BinarySerialize α] : BinarySerialize (TwoPSet α) where
  encode tps :=
    BinarySerialize.encode tps.added ++ BinarySerialize.encode tps.removed
  decode bytes offset := do
    let (added, offset') ← BinarySerialize.decode bytes offset
    let (removed, consumed) ← BinarySerialize.decode bytes offset'
    return ({ added, removed }, consumed)

instance [BinarySerialize α] : BinarySerialize (TwoPSetOp α) where
  encode op := match op with
    | .add value => ByteArray.mk #[0] ++ BinarySerialize.encode value
    | .remove value => ByteArray.mk #[1] ++ BinarySerialize.encode value
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    let (value, consumed) ← BinarySerialize.decode bytes (offset + 1)
    match tag with
    | 0 => return (.add value, consumed)
    | 1 => return (.remove value, consumed)
    | _ => none

/-! ## ORSet -/

instance [BEq α] [Hashable α] [BinarySerialize α] : BinarySerialize (ORSet α) where
  encode os := BinarySerialize.encode os.elements.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ elements := Std.HashMap.ofList list }, consumed)

instance [BinarySerialize α] : BinarySerialize (ORSetOp α) where
  encode op := match op with
    | .add value tag =>
      ByteArray.mk #[0] ++ BinarySerialize.encode value ++ BinarySerialize.encode tag
    | .remove value observedTags =>
      ByteArray.mk #[1] ++ BinarySerialize.encode value ++ BinarySerialize.encode observedTags
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (value, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (uniqueTag, consumed) ← BinarySerialize.decode bytes offset'
      return (.add value uniqueTag, consumed)
    | 1 =>
      let (value, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (observedTags, consumed) ← BinarySerialize.decode bytes offset'
      return (.remove value observedTags, consumed)
    | _ => none

/-! ## LWWElementSet -/

instance [BEq α] [Hashable α] [BinarySerialize α] : BinarySerialize (LWWElementSet α) where
  encode set := BinarySerialize.encode set.entries.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ entries := Std.HashMap.ofList list }, consumed)

instance [BinarySerialize α] : BinarySerialize (LWWElementSetOp α) where
  encode op := match op with
    | .add value timestamp =>
      ByteArray.mk #[0] ++ BinarySerialize.encode value ++ BinarySerialize.encode timestamp
    | .remove value timestamp =>
      ByteArray.mk #[1] ++ BinarySerialize.encode value ++ BinarySerialize.encode timestamp
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    let (value, offset') ← BinarySerialize.decode bytes (offset + 1)
    let (timestamp, consumed) ← BinarySerialize.decode bytes offset'
    match tag with
    | 0 => return (.add value timestamp, consumed)
    | 1 => return (.remove value timestamp, consumed)
    | _ => none

end Convergent.Serialization
