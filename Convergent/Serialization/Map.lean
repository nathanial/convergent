/-
  Binary Serialization for Map CRDTs

  Provides BinarySerialize instances for:
  - LWWMap, LWWMapOp
  - ORMap, ORMapOp
  - PNMap, PNMapOp
-/
import Convergent.Serialization.Counter
import Convergent.Map.LWWMap
import Convergent.Map.ORMap
import Convergent.Map.PNMap

namespace Convergent.Serialization

open Convergent

/-! ## LWWMap -/

instance [BEq κ] [Hashable κ] [BinarySerialize κ] [BinarySerialize α] :
    BinarySerialize (LWWMap κ α) where
  encode m := BinarySerialize.encode m.entries.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ entries := Std.HashMap.ofList list }, consumed)

instance [BinarySerialize κ] [BinarySerialize α] : BinarySerialize (LWWMapOp κ α) where
  encode op := match op with
    | .put key value timestamp =>
      ByteArray.mk #[0] ++ BinarySerialize.encode key ++
        BinarySerialize.encode value ++ BinarySerialize.encode timestamp
    | .delete key timestamp =>
      ByteArray.mk #[1] ++ BinarySerialize.encode key ++ BinarySerialize.encode timestamp
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (key, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (value, offset'') ← BinarySerialize.decode bytes offset'
      let (timestamp, consumed) ← BinarySerialize.decode bytes offset''
      return (.put key value timestamp, consumed)
    | 1 =>
      let (key, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (timestamp, consumed) ← BinarySerialize.decode bytes offset'
      return (.delete key timestamp, consumed)
    | _ => none

/-! ## ORMap -/

instance [BEq κ] [Hashable κ] [BinarySerialize κ] [BinarySerialize α] :
    BinarySerialize (ORMap κ α OpA) where
  encode m := BinarySerialize.encode m.entries.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ entries := Std.HashMap.ofList list }, consumed)

instance [BinarySerialize κ] [BinarySerialize α] [BinarySerialize OpA] :
    BinarySerialize (ORMapOp κ α OpA) where
  encode op := match op with
    | .put key value tag =>
      ByteArray.mk #[0] ++ BinarySerialize.encode key ++
        BinarySerialize.encode value ++ BinarySerialize.encode tag
    | .delete key observedTags =>
      ByteArray.mk #[1] ++ BinarySerialize.encode key ++ BinarySerialize.encode observedTags
    | .update key tag nestedOp =>
      ByteArray.mk #[2] ++ BinarySerialize.encode key ++
        BinarySerialize.encode tag ++ BinarySerialize.encode nestedOp
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (key, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (value, offset'') ← BinarySerialize.decode bytes offset'
      let (uniqueTag, consumed) ← BinarySerialize.decode bytes offset''
      return (.put key value uniqueTag, consumed)
    | 1 =>
      let (key, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (observedTags, consumed) ← BinarySerialize.decode bytes offset'
      return (.delete key observedTags, consumed)
    | 2 =>
      let (key, offset') ← BinarySerialize.decode bytes (offset + 1)
      let (uniqueTag, offset'') ← BinarySerialize.decode bytes offset'
      let (nestedOp, consumed) ← BinarySerialize.decode bytes offset''
      return (.update key uniqueTag nestedOp, consumed)
    | _ => none

/-! ## PNMap -/

instance [BEq κ] [Hashable κ] [BinarySerialize κ] : BinarySerialize (PNMap κ) where
  encode m := BinarySerialize.encode m.entries.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return ({ entries := Std.HashMap.ofList list }, consumed)

instance [BinarySerialize κ] : BinarySerialize (PNMapOp κ) where
  encode op := match op with
    | .increment key replica =>
      ByteArray.mk #[0] ++ BinarySerialize.encode key ++ BinarySerialize.encode replica
    | .decrement key replica =>
      ByteArray.mk #[1] ++ BinarySerialize.encode key ++ BinarySerialize.encode replica
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    let (key, offset') ← BinarySerialize.decode bytes (offset + 1)
    let (replica, consumed) ← BinarySerialize.decode bytes offset'
    match tag with
    | 0 => return (.increment key replica, consumed)
    | 1 => return (.decrement key replica, consumed)
    | _ => none

end Convergent.Serialization
