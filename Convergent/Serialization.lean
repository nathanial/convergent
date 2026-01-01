/-
  Convergent Serialization

  Re-exports all binary serialization modules for CRDT types.

  This module provides `BinarySerialize` instances for all 19 CRDT types
  in the Convergent library, enabling network transmission and persistence.

  ## Usage

  ```lean
  import Convergent
  import Convergent.Serialization

  open Convergent Convergent.Serialization

  -- Encode a GCounter
  let counter := GCounter.empty |> fun s => GCounter.apply s (GCounter.increment 1)
  let bytes := BinarySerialize.encode counter

  -- Decode a GCounter
  match BinarySerialize.decodeExact bytes with
  | some decoded => -- use decoded
  | none => -- handle error
  ```

  ## Encoding Details

  - **Nat**: LEB128-style variable-length encoding
  - **Int**: ZigZag encoding + LEB128
  - **Inductive types**: Tag byte for constructor + field values
  - **Containers**: Length prefix + elements
  - **HashMap/HashSet**: Serialized as sorted lists
-/
import Convergent.Serialization.Binary
import Convergent.Serialization.Core
import Convergent.Serialization.Counter
import Convergent.Serialization.Register
import Convergent.Serialization.Set
import Convergent.Serialization.Map
import Convergent.Serialization.Sequence
import Convergent.Serialization.Flag
import Convergent.Serialization.Graph
