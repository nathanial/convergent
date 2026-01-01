/-
  Binary Serialization for Counter CRDTs

  Provides BinarySerialize instances for:
  - GCounter, GCounterOp
  - PNCounter, PNCounterOp
-/
import Convergent.Serialization.Core
import Convergent.Counter.GCounter
import Convergent.Counter.PNCounter

namespace Convergent.Serialization

open Convergent

/-! ## GCounter -/

instance : BinarySerialize GCounter where
  encode gc := BinarySerialize.encode gc.counts
  decode bytes offset := do
    let (counts, consumed) ← BinarySerialize.decode bytes offset
    return ({ counts }, consumed)

instance : BinarySerialize GCounterOp where
  encode op :=
    BinarySerialize.encode op.replica ++ encodeNat op.amount
  decode bytes offset := do
    let (replica, offset') ← BinarySerialize.decode bytes offset
    let (amount, consumed) ← decodeNat bytes offset'
    return ({ replica, amount }, consumed)

/-! ## PNCounter -/

instance : BinarySerialize PNCounter where
  encode pn :=
    BinarySerialize.encode pn.positive ++ BinarySerialize.encode pn.negative
  decode bytes offset := do
    let (positive, offset') ← BinarySerialize.decode bytes offset
    let (negative, consumed) ← BinarySerialize.decode bytes offset'
    return ({ positive, negative }, consumed)

instance : BinarySerialize PNCounterOp where
  encode op := match op with
    | .increment replica amount =>
      ByteArray.mk #[0] ++ BinarySerialize.encode replica ++ encodeNat amount
    | .decrement replica amount =>
      ByteArray.mk #[1] ++ BinarySerialize.encode replica ++ encodeNat amount
  decode bytes offset := do
    guard (offset < bytes.size)
    let tag := bytes.get! offset
    let (replica, offset') ← BinarySerialize.decode bytes (offset + 1)
    let (amount, consumed) ← decodeNat bytes offset'
    match tag with
    | 0 => return (.increment replica amount, consumed)
    | 1 => return (.decrement replica amount, consumed)
    | _ => none

end Convergent.Serialization
