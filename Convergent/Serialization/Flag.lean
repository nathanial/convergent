/-
  Binary Serialization for Flag CRDTs

  Provides BinarySerialize instances for:
  - EWFlag, EWFlagOp
  - DWFlag, DWFlagOp
-/
import Convergent.Serialization.Set
import Convergent.Flag.EWFlag
import Convergent.Flag.DWFlag

namespace Convergent.Serialization

open Convergent

/-! ## EWFlag -/

instance : BinarySerialize EWFlag where
  encode f :=
    BinarySerialize.encode f.lastEnable ++ BinarySerialize.encode f.lastDisable
  decode bytes offset := do
    let (lastEnable, offset') ← BinarySerialize.decode bytes offset
    let (lastDisable, consumed) ← BinarySerialize.decode bytes offset'
    return ({ lastEnable, lastDisable }, consumed)

instance : BinarySerialize EWFlagOp where
  encode op := match op with
    | .enable timestamp => ByteArray.mk #[0] ++ BinarySerialize.encode timestamp
    | .disable timestamp => ByteArray.mk #[1] ++ BinarySerialize.encode timestamp
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (timestamp, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.enable timestamp, consumed)
    | 1 =>
      let (timestamp, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.disable timestamp, consumed)
    | _ => none

/-! ## DWFlag -/

instance : BinarySerialize DWFlag where
  encode f :=
    BinarySerialize.encode f.lastEnable ++ BinarySerialize.encode f.lastDisable
  decode bytes offset := do
    let (lastEnable, offset') ← BinarySerialize.decode bytes offset
    let (lastDisable, consumed) ← BinarySerialize.decode bytes offset'
    return ({ lastEnable, lastDisable }, consumed)

instance : BinarySerialize DWFlagOp where
  encode op := match op with
    | .enable timestamp => ByteArray.mk #[0] ++ BinarySerialize.encode timestamp
    | .disable timestamp => ByteArray.mk #[1] ++ BinarySerialize.encode timestamp
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    match tag with
    | 0 =>
      let (timestamp, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.enable timestamp, consumed)
    | 1 =>
      let (timestamp, consumed) ← BinarySerialize.decode bytes (offset + 1)
      return (.disable timestamp, consumed)
    | _ => none

end Convergent.Serialization
