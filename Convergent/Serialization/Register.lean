/-
  Binary Serialization for Register CRDTs

  Provides BinarySerialize instances for:
  - LWWRegister, LWWRegisterOp
  - MVRegister, MVRegisterOp
-/
import Convergent.Serialization.Core
import Convergent.Register.LWWRegister
import Convergent.Register.MVRegister

namespace Convergent.Serialization

open Convergent

/-! ## LWWRegister -/

instance [BinarySerialize α] : BinarySerialize (LWWRegister α) where
  encode reg := BinarySerialize.encode reg.value
  decode bytes offset := do
    let (value, consumed) ← BinarySerialize.decode bytes offset
    return ({ value }, consumed)

instance [BinarySerialize α] : BinarySerialize (LWWRegisterOp α) where
  encode op :=
    BinarySerialize.encode op.value ++ BinarySerialize.encode op.timestamp
  decode bytes offset := do
    let (value, offset') ← BinarySerialize.decode bytes offset
    let (timestamp, consumed) ← BinarySerialize.decode bytes offset'
    return ({ value, timestamp }, consumed)

/-! ## MVRegister -/

instance [BinarySerialize α] : BinarySerialize (MVRegister α) where
  encode reg := BinarySerialize.encode reg.values
  decode bytes offset := do
    let (values, consumed) ← BinarySerialize.decode bytes offset
    return ({ values }, consumed)

instance [BinarySerialize α] : BinarySerialize (MVRegisterOp α) where
  encode op :=
    BinarySerialize.encode op.value ++ BinarySerialize.encode op.clock
  decode bytes offset := do
    let (value, offset') ← BinarySerialize.decode bytes offset
    let (clock, consumed) ← BinarySerialize.decode bytes offset'
    return ({ value, clock }, consumed)

end Convergent.Serialization
