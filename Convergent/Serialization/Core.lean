/-
  Binary Serialization for Core CRDT Types

  Provides BinarySerialize instances for:
  - ReplicaId
  - UniqueId
  - UniqueIdGen
  - LamportTs
  - VectorClock
-/
import Convergent.Serialization.Binary
import Convergent.Core.ReplicaId
import Convergent.Core.UniqueId
import Convergent.Core.Timestamp

namespace Convergent.Serialization

open Convergent

/-! ## ReplicaId -/

instance : BinarySerialize ReplicaId where
  encode r := encodeNat r.id
  decode bytes offset := do
    let (id, consumed) ← decodeNat bytes offset
    return ({ id }, consumed)

/-! ## UniqueId -/

instance : BinarySerialize UniqueId where
  encode uid :=
    BinarySerialize.encode uid.replica ++ encodeNat uid.seq
  decode bytes offset := do
    let (replica, offset') ← BinarySerialize.decode bytes offset
    let (seq, consumed) ← decodeNat bytes offset'
    return ({ replica, seq }, consumed)

/-! ## UniqueIdGen -/

instance : BinarySerialize UniqueIdGen where
  encode gen :=
    BinarySerialize.encode gen.replica ++ encodeNat gen.nextSeq
  decode bytes offset := do
    let (replica, offset') ← BinarySerialize.decode bytes offset
    let (nextSeq, consumed) ← decodeNat bytes offset'
    return ({ replica, nextSeq }, consumed)

/-! ## LamportTs -/

instance : BinarySerialize LamportTs where
  encode ts :=
    encodeNat ts.time ++ BinarySerialize.encode ts.replica
  decode bytes offset := do
    let (time, offset') ← decodeNat bytes offset
    let (replica, consumed) ← BinarySerialize.decode bytes offset'
    return ({ time, replica }, consumed)

/-! ## VectorClock -/

instance : BinarySerialize VectorClock where
  encode vc := BinarySerialize.encode vc.clocks
  decode bytes offset := do
    let (clocks, consumed) ← BinarySerialize.decode bytes offset
    return ({ clocks }, consumed)

end Convergent.Serialization
