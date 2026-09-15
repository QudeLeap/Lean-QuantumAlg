/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Util.Classical.NumberTheory.Extended

/-!
# Original unsigned, signed and right-nested XGCD encodings

The original pure representation declarations retain their exact names,
shapes, encoders, decoders and proof bodies. This owner has no retired machine
interpreter dependency and makes no claim about execution or resource costs.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory

open ClassicalAlgorithms ClassicalAlgorithms.NumberTheory

/-! ## Unsigned words and pairs -/

/-- Semantic carrier for one unsigned fixed-width word. -/
abbrev WordValue (width : Nat) :=
  ClassicalAlgorithms.Word width

/-- The shared closed shape for two equal-width unsigned words. -/
abbrev WordPairShape (width : Nat) : CShape :=
  .product (.unsignedWord width) (.unsignedWord width)

/-- Semantic counterpart of `WordPairShape`. -/
abbrev WordPairValue (width : Nat) :=
  WordValue width × WordValue width

/-- Relate a nominal unsigned word to its intrinsic finite-word value. -/
def WordRepresents {width : Nat} (encoded : CShape.Word width)
    (value : WordValue width) : Prop :=
  decodeWord encoded = value

/-- Encode two intrinsic words without flattening their product structure. -/
def encodeWordPair {width : Nat} (value : WordPairValue width) :
    CShape.Value (WordPairShape width) :=
  .product (encodeWord value.1) (encodeWord value.2)

/-- Decode the two fields of one nominal word pair. -/
def decodeWordPair {width : Nat}
    (encoded : CShape.Value (WordPairShape width)) : WordPairValue width :=
  (decodeWord encoded.first, decodeWord encoded.second)

/-- Relate one nominal pair to its semantic unsigned operands. -/
def WordPairRepresents {width : Nat}
    (encoded : CShape.Value (WordPairShape width))
    (value : WordPairValue width) : Prop :=
  decodeWordPair encoded = value

theorem encodeWord_represents {width : Nat} (value : WordValue width) :
    WordRepresents (encodeWord value) value :=
  rfl

@[simp] theorem decode_encode_wordPair {width : Nat}
    (value : WordPairValue width) :
    decodeWordPair (encodeWordPair value) = value := by
  cases value
  rfl

@[simp] theorem encode_decode_wordPair {width : Nat}
    (encoded : CShape.Value (WordPairShape width)) :
    encodeWordPair (decodeWordPair encoded) = encoded := by
  cases encoded with
  | product left right =>
      cases left
      cases right
      rfl

theorem encodeWordPair_represents {width : Nat}
    (value : WordPairValue width) :
    WordPairRepresents (encodeWordPair value) value := by
  simp [WordPairRepresents]

/-! ## Bounded signed words -/

/-- Nominal machine shape for one two's-complement signed value. -/
abbrev SignedShape (width : Nat) : CShape :=
  .boundedSignedWord width

/-- Encode the exact raw word owned by the semantic signed carrier. -/
def encodeSigned {width : Nat} (value : BoundedSigned width) :
    CShape.Value (SignedShape width) :=
  .boundedSignedWord value.encode

/-- Interpret a nominal signed word through the pure two's-complement carrier. -/
def decodeSigned {width : Nat}
    (encoded : CShape.Value (SignedShape width)) : BoundedSigned width :=
  BoundedSigned.decode encoded.boundedSignedEncoding

/-- The semantic witness relation for a raw nominal signed encoding. -/
def SignedRepresents {width : Nat}
    (encoded : CShape.Value (SignedShape width))
    (value : BoundedSigned width) : Prop :=
  decodeSigned encoded = value

/-- Signed encoding is exactly Core's raw nominal packing boundary. -/
theorem encodeSigned_eq_packBoundedSignedWord {width : Nat}
    (value : BoundedSigned width) :
    encodeSigned value =
      CShape.packBoundedSignedWord width (encodeWord value.encode) :=
  rfl

@[simp] theorem decode_encode_signed {width : Nat}
    (value : BoundedSigned width) :
    decodeSigned (encodeSigned value) = value := by
  exact BoundedSigned.decode_encode value

@[simp] theorem encode_decode_signed {width : Nat}
    (encoded : CShape.Value (SignedShape width)) :
    encodeSigned (decodeSigned encoded) = encoded := by
  cases encoded with
  | boundedSignedWord _ => rfl

theorem encodeSigned_represents {width : Nat}
    (value : BoundedSigned width) :
    SignedRepresents (encodeSigned value) value := by
  simp [SignedRepresents]

theorem signedRepresents_iff_encoding_eq {width : Nat}
    {encoded : CShape.Value (SignedShape width)}
    {value : BoundedSigned width} :
    SignedRepresents encoded value ↔
      encoded.boundedSignedEncoding = value.encode := by
  constructor
  · intro represents
    have := congrArg BoundedSigned.encode represents
    simpa [SignedRepresents, decodeSigned] using this
  · intro encoding
    apply BoundedSigned.ext
    apply BitVec.toFin_injective
    simpa [decodeSigned, BoundedSigned.decode, BoundedSigned.encode] using encoding

/-! ## Right-nested XGCD results -/

/-- Semantic tuple used by the shared XGCD representation boundary.

Concrete pure XGCD structures may bridge to this tuple without making this
module depend on one coefficient-field naming convention. -/
abbrev XGCDTuple (width : Nat) :=
  WordValue width ×
    (BoundedSigned (coefficientWidth width) ×
      BoundedSigned (coefficientWidth width))

/-- Closed, right-nested result shape: gcd, then the two signed coefficients. -/
abbrev XGCDOutputShape (width : Nat) : CShape :=
  .product (.unsignedWord width)
    (.product (SignedShape (coefficientWidth width))
      (SignedShape (coefficientWidth width)))

/-- Encode the semantic XGCD tuple with the frozen right nesting. -/
def encodeXGCDTuple {width : Nat} (value : XGCDTuple width) :
    CShape.Value (XGCDOutputShape width) :=
  .product (encodeWord value.1)
    (.product (encodeSigned value.2.1) (encodeSigned value.2.2))

/-- Decode all three fields of the frozen right-nested XGCD shape. -/
def decodeXGCDTuple {width : Nat}
    (encoded : CShape.Value (XGCDOutputShape width)) : XGCDTuple width :=
  (decodeWord encoded.first,
    (decodeSigned encoded.second.first, decodeSigned encoded.second.second))

/-- Relate a right-nested machine output to its semantic XGCD tuple. -/
def XGCDTupleRepresents {width : Nat}
    (encoded : CShape.Value (XGCDOutputShape width))
    (value : XGCDTuple width) : Prop :=
  decodeXGCDTuple encoded = value

@[simp] theorem decode_encode_xgcdTuple {width : Nat}
    (value : XGCDTuple width) :
    decodeXGCDTuple (encodeXGCDTuple value) = value := by
  rcases value with ⟨gcd, left, right⟩
  rfl

@[simp] theorem encode_decode_xgcdTuple {width : Nat}
    (encoded : CShape.Value (XGCDOutputShape width)) :
    encodeXGCDTuple (decodeXGCDTuple encoded) = encoded := by
  cases encoded with
  | product gcd coefficients =>
      cases gcd
      cases coefficients with
      | product left right =>
          cases left
          cases right
          rfl

theorem encodeXGCDTuple_represents {width : Nat}
    (value : XGCDTuple width) :
    XGCDTupleRepresents (encodeXGCDTuple value) value := by
  simp [XGCDTupleRepresents]

end QuantumAlg.ClassicalRoutines.NumberTheory
