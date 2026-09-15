/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.Arithmetic

/-! Closed-word encoding for the pure fixed-width arithmetic carrier. -/

namespace QuantumAlg.ClassicalRoutines

/-- Encode a pure fixed-width word as the corresponding closed machine word. -/
def encodeWord {width : Nat}
    (word : ClassicalAlgorithms.Word width) : CShape.Word width :=
  .unsignedWord word

/-- Decode a closed machine word to the shared pure fixed-width carrier. -/
def decodeWord {width : Nat} (word : CShape.Word width) :
    ClassicalAlgorithms.Word width :=
  match word with
  | .unsignedWord value => value

@[simp] theorem fixedWidthDecode_encode_word {width : Nat}
    (word : ClassicalAlgorithms.Word width) :
    decodeWord (encodeWord word) = word :=
  rfl

@[simp] theorem fixedWidthEncode_decode_word {width : Nat}
    (word : CShape.Word width) :
    encodeWord (decodeWord word) = word := by
  cases word
  rfl

end QuantumAlg.ClassicalRoutines
