/-
  Binary Serialization Framework

  Provides a typeclass for binary serialization of CRDT types.
  Uses LEB128-style variable-length encoding for Nat values.
-/
import Std.Data.HashMap
import Std.Data.HashSet

namespace Convergent.Serialization

/-- Binary serialization typeclass -/
class BinarySerialize (α : Type) where
  /-- Encode a value to bytes -/
  encode : α → ByteArray
  /-- Decode bytes, returning the value and number of bytes consumed -/
  decode : ByteArray → Nat → Option (α × Nat)

namespace BinarySerialize

variable {α : Type} [BinarySerialize α]

/-- Decode from the start of a ByteArray -/
def decodeFrom (bytes : ByteArray) : Option (α × Nat) :=
  decode bytes 0

/-- Decode exactly the entire ByteArray -/
def decodeExact (bytes : ByteArray) : Option α := do
  let (val, consumed) ← decode bytes 0
  guard (consumed == bytes.size)
  return val

/-- Round-trip test helper -/
def roundTrip (val : α) : Option α :=
  decodeExact (encode val)

end BinarySerialize

/-! ## Primitive Instances -/

/-- Encode a Nat using LEB128-style variable-length encoding -/
partial def encodeNat (n : Nat) : ByteArray :=
  if n < 128 then
    ByteArray.mk #[n.toUInt8]
  else
    let byte := (n % 128 + 128).toUInt8  -- Set high bit to indicate more bytes
    ByteArray.mk #[byte] ++ encodeNat (n / 128)

/-- Decode a LEB128-encoded Nat -/
partial def decodeNat (bytes : ByteArray) (offset : Nat) : Option (Nat × Nat) :=
  go bytes offset 0 0
where
  go (bytes : ByteArray) (offset shift : Nat) (acc : Nat) : Option (Nat × Nat) :=
    if offset >= bytes.size then none
    else
      let byte := bytes.get! offset
      let value := (byte.toNat &&& 0x7F) <<< shift
      let acc' := acc + value
      if byte.toNat < 128 then
        some (acc', offset + 1)
      else
        go bytes (offset + 1) (shift + 7) acc'

instance : BinarySerialize Nat where
  encode := encodeNat
  decode := decodeNat

/-- Encode Int using ZigZag encoding, then LEB128 -/
def encodeInt (n : Int) : ByteArray :=
  -- ZigZag: (n << 1) ^ (n >> 63) maps negative to odd, positive to even
  let zigzag := if n >= 0 then (2 * n.toNat) else (2 * (-n - 1).toNat + 1)
  encodeNat zigzag

/-- Decode ZigZag-encoded Int -/
def decodeInt (bytes : ByteArray) (offset : Nat) : Option (Int × Nat) := do
  let (zigzag, consumed) ← decodeNat bytes offset
  -- Reverse ZigZag
  let n := if zigzag % 2 == 0 then
    Int.ofNat (zigzag / 2)
  else
    -Int.ofNat (zigzag / 2 + 1)
  return (n, consumed)

instance : BinarySerialize Int where
  encode := encodeInt
  decode := decodeInt

instance : BinarySerialize Bool where
  encode b := ByteArray.mk #[if b then 1 else 0]
  decode bytes offset :=
    if offset >= bytes.size then none
    else some (bytes.get! offset != 0, offset + 1)

instance : BinarySerialize UInt8 where
  encode b := ByteArray.mk #[b]
  decode bytes offset :=
    if offset >= bytes.size then none
    else some (bytes.get! offset, offset + 1)

instance : BinarySerialize Char where
  encode c := encodeNat c.toNat
  decode bytes offset := do
    let (n, consumed) ← decodeNat bytes offset
    if n < UInt32.size then
      return (Char.ofNat n, consumed)
    else
      none

instance : BinarySerialize String where
  encode s :=
    let bytes := s.toUTF8
    encodeNat bytes.size ++ bytes
  decode bytes offset := do
    let (len, offset') ← decodeNat bytes offset
    guard (offset' + len <= bytes.size)
    let strBytes := bytes.extract offset' (offset' + len)
    return (String.fromUTF8! strBytes, offset' + len)

/-! ## Container Instances -/

instance [BinarySerialize α] : BinarySerialize (Option α) where
  encode opt := match opt with
    | none => ByteArray.mk #[0]
    | some val => ByteArray.mk #[1] ++ BinarySerialize.encode val
  decode bytes offset := do
    guard (offset < bytes.size)
    match bytes.get! offset with
    | 0 => some (none, offset + 1)
    | 1 =>
      let (val, consumed) ← BinarySerialize.decode bytes (offset + 1)
      some (some val, consumed)
    | _ => none

instance [BinarySerialize α] [BinarySerialize β] : BinarySerialize (α × β) where
  encode pair :=
    BinarySerialize.encode pair.1 ++ BinarySerialize.encode pair.2
  decode bytes offset := do
    let (a, offset') ← BinarySerialize.decode bytes offset
    let (b, offset'') ← BinarySerialize.decode bytes offset'
    return ((a, b), offset'')

instance [BinarySerialize α] : BinarySerialize (List α) where
  encode list :=
    let header := encodeNat list.length
    list.foldl (fun acc elem => acc ++ BinarySerialize.encode elem) header
  decode bytes offset := do
    let (len, offset') ← decodeNat bytes offset
    let mut result : List α := []
    let mut currentOffset := offset'
    for _ in [0:len] do
      let (elem, newOffset) ← BinarySerialize.decode bytes currentOffset
      result := result ++ [elem]
      currentOffset := newOffset
    return (result, currentOffset)

instance [BinarySerialize α] : BinarySerialize (Array α) where
  encode arr := BinarySerialize.encode arr.toList
  decode bytes offset := do
    let (list, consumed) ← (BinarySerialize.decode bytes offset : Option (List α × Nat))
    return (list.toArray, consumed)

/-! ## HashMap and HashSet Instances -/

instance [BinarySerialize κ] [BinarySerialize α] [BEq κ] [Hashable κ] :
    BinarySerialize (Std.HashMap κ α) where
  encode m := BinarySerialize.encode m.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return (Std.HashMap.ofList list, consumed)

instance [BinarySerialize α] [BEq α] [Hashable α] :
    BinarySerialize (Std.HashSet α) where
  encode s := BinarySerialize.encode s.toList
  decode bytes offset := do
    let (list, consumed) ← BinarySerialize.decode bytes offset
    return (Std.HashSet.ofList list, consumed)

/-! ## ByteArray utilities -/

/-- Concatenate ByteArrays -/
def ByteArray.concat (arrays : List ByteArray) : ByteArray :=
  arrays.foldl (· ++ ·) ByteArray.empty

end Convergent.Serialization
