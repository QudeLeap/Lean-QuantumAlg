/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Model
import all QuantumAlg.Components.Classical.Word

/-!
# Original raw signed coefficient representation

The existing two's-complement modulo invariant composes through the actual
word resize, increment, low product, and wrapping subtraction operations.
Exact signed decoding retains its original positive-width and signed-range
premises. These word equations introduce no circuit or resource assumption.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open ClassicalAlgorithms
open ClassicalAlgorithms.NumberTheory

/-- Interpret one raw execution-width word using the shared two's-complement
carrier.  Keeping this decoder public lets checked modular routines consume the
pre-packing engine without inventing a second signed interpretation. -/
def decodeRawSignedWord {width : Nat}
    (encoded : CShape.Word (PureXGCD.executionCoefficientWidth width)) : Int :=
  (BoundedSigned.decode (decodeWord encoded)).toInt

/-- A raw word represents an integer modulo its two's-complement modulus.
This is the compositional invariant used by `mulLow` and wrapping subtraction;
exact signed decoding is recovered only when a range proof is available. -/
def RawSignedRepresents {signedWidth : Nat}
    (encoded : CShape.Word signedWidth) (value : Int) : Prop :=
  Int.ModEq (CShape.wordModulus signedWidth : Int)
    (encoded.toNat : Int) value

private lemma ofInt_rawSignedRepresents (signedWidth : Nat) (value : Int) :
    RawSignedRepresents
      (encodeWord (BoundedSigned.ofInt signedWidth value).encode) value := by
  unfold RawSignedRepresents Int.ModEq
  change
    (((value % (2 ^ signedWidth : Int)).toNat : Nat) : Int) %
        (2 ^ signedWidth : Int) =
      value % (2 ^ signedWidth : Int)
  have modulusNe : (2 ^ signedWidth : Int) ≠ 0 := by
    positivity
  rw [Int.toNat_of_nonneg (Int.emod_nonneg value modulusNe)]
  exact Int.emod_emod value (2 ^ signedWidth : Int)

/-- A modulo-represented integer in the signed interval decodes exactly. -/
lemma rawSignedRepresents_decode_eq {signedWidth : Nat}
    (encoded : CShape.Word signedWidth) (value : Int)
    (widthPositive : 0 < signedWidth)
    (represents : RawSignedRepresents encoded value)
    (range :
      ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
        signedWidth value) :
    (BoundedSigned.decode (decodeWord encoded)).toInt = value := by
  cases encoded with
  | unsignedWord bits =>
      change (BoundedSigned.decode bits).toInt = value
      change
        (bits.val : Int) ≡ value
          [ZMOD (CShape.wordModulus signedWidth : Int)]
        at represents
      have canonical := ofInt_rawSignedRepresents signedWidth value
      change
        ((BoundedSigned.ofInt signedWidth value).encode.val : Int) ≡ value
          [ZMOD (CShape.wordModulus signedWidth : Int)]
        at canonical
      have integerCongruence :
          (bits.val : Int) ≡
              ((BoundedSigned.ofInt signedWidth value).encode.val : Int)
            [ZMOD (CShape.wordModulus signedWidth : Int)] := by
        exact represents.trans canonical.symm
      have naturalCongruence :
          bits.val ≡ (BoundedSigned.ofInt signedWidth value).encode.val
            [MOD CShape.wordModulus signedWidth] := by
        exact Int.natCast_modEq_iff.mp integerCongruence
      have encodingEq :
          bits = (BoundedSigned.ofInt signedWidth value).encode := by
        apply Fin.ext
        exact naturalCongruence.eq_of_lt_of_lt bits.isLt
          (BoundedSigned.ofInt signedWidth value).encode.isLt
      rw [encodingEq, BoundedSigned.decode_encode]
      exact BoundedSigned.toInt_ofInt_eq_self
        widthPositive range.1 range.2

private lemma rawSignedRepresents_wordResize
    {sourceWidth signedWidth : Nat} (input : CShape.Word sourceWidth) :
    RawSignedRepresents (CShape.wordResize signedWidth input)
      (input.toNat : Int) := by
  cases input with
  | unsignedWord bits =>
      change
        ((bits.val % CShape.wordModulus signedWidth : Nat) : Int) ≡
            (bits.val : Int)
          [ZMOD (CShape.wordModulus signedWidth : Int)]
      have naturalCongruence :
          bits.val % CShape.wordModulus signedWidth ≡ bits.val
            [MOD CShape.wordModulus signedWidth] :=
        Nat.mod_modEq bits.val (CShape.wordModulus signedWidth)
      exact Int.natCast_modEq_iff.mpr naturalCongruence

/-- Narrowing a raw signed word to any no-wider target produces exactly the
target-width two's-complement encoding of the same represented integer. -/
private lemma wordResize_eq_ofInt_of_rawSignedRepresents
    {sourceWidth targetWidth : Nat} (widthLe : targetWidth ≤ sourceWidth)
    (input : CShape.Word sourceWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    CShape.wordResize targetWidth input =
      encodeWord (BoundedSigned.ofInt targetWidth value).encode := by
  cases input with
  | unsignedWord bits =>
      change
        (bits.val : Int) ≡ value
          [ZMOD (CShape.wordModulus sourceWidth : Int)]
        at represents
      have modulusDvd :
          (CShape.wordModulus targetWidth : Int) ∣
            (CShape.wordModulus sourceWidth : Int) := by
        exact Int.natCast_dvd_natCast.mpr (by
          simpa [CShape.wordModulus] using pow_dvd_pow 2 widthLe)
      have targetCongruence :
          (bits.val : Int) ≡ value
            [ZMOD (CShape.wordModulus targetWidth : Int)] :=
        represents.of_dvd modulusDvd
      have encodedCongruence :=
        ofInt_rawSignedRepresents targetWidth value
      change
        ((BoundedSigned.ofInt targetWidth value).encode.val : Int) ≡ value
          [ZMOD (CShape.wordModulus targetWidth : Int)]
        at encodedCongruence
      have rawToEncoded :
          bits.val ≡ (BoundedSigned.ofInt targetWidth value).encode.val
            [MOD CShape.wordModulus targetWidth] := by
        exact Int.natCast_modEq_iff.mp
          (targetCongruence.trans encodedCongruence.symm)
      have resizedToRaw :
          bits.val % CShape.wordModulus targetWidth ≡ bits.val
            [MOD CShape.wordModulus targetWidth] :=
        Nat.mod_modEq bits.val (CShape.wordModulus targetWidth)
      unfold CShape.wordResize CShape.wordOfNat encodeWord
      congr 1
      apply Fin.ext
      exact (resizedToRaw.trans rawToEncoded).eq_of_lt_of_lt
        (Nat.mod_lt bits.val (CShape.wordModulus_pos targetWidth))
        (BoundedSigned.ofInt targetWidth value).encode.isLt

private lemma rawSignedRepresents_increment {signedWidth : Nat}
    (input : CShape.Word signedWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .increment signedWidth input)
      (value + 1) := by
  cases input with
  | unsignedWord bits =>
      change
        (bits.val : Int) ≡ value
          [ZMOD (CShape.wordModulus signedWidth : Int)]
        at represents
      change
        (((bits.val + 1) % CShape.wordModulus signedWidth : Nat) : Int) ≡
            value + 1
          [ZMOD (CShape.wordModulus signedWidth : Int)]
      have naturalCongruence :
          (bits.val + 1) % CShape.wordModulus signedWidth ≡ bits.val + 1
            [MOD CShape.wordModulus signedWidth] :=
        Nat.mod_modEq (bits.val + 1) (CShape.wordModulus signedWidth)
      have integerCongruence := Int.natCast_modEq_iff.mpr naturalCongruence
      have valueCongruence := represents.add (Int.ModEq.refl 1)
      simpa only [Nat.cast_add, Nat.cast_one] using
        integerCongruence.trans valueCongruence

private lemma rawSignedRepresents_mulLow {signedWidth : Nat}
    (left right : CShape.Word signedWidth) (leftValue rightValue : Int)
    (leftRepresents : RawSignedRepresents left leftValue)
    (rightRepresents : RawSignedRepresents right rightValue) :
    RawSignedRepresents
      (Resource.WordBinaryOpcode.eval .mulLow signedWidth
        (.product left right))
      (leftValue * rightValue) := by
  cases left with
  | unsignedWord leftBits =>
      cases right with
      | unsignedWord rightBits =>
          change
            (leftBits.val : Int) ≡ leftValue
              [ZMOD (CShape.wordModulus signedWidth : Int)]
            at leftRepresents
          change
            (rightBits.val : Int) ≡ rightValue
              [ZMOD (CShape.wordModulus signedWidth : Int)]
            at rightRepresents
          change
            (((leftBits.val * rightBits.val) %
                  CShape.wordModulus signedWidth : Nat) : Int) ≡
                leftValue * rightValue
              [ZMOD (CShape.wordModulus signedWidth : Int)]
          have naturalCongruence :
              (leftBits.val * rightBits.val) %
                    CShape.wordModulus signedWidth ≡
                  leftBits.val * rightBits.val
                [MOD CShape.wordModulus signedWidth] :=
            Nat.mod_modEq (leftBits.val * rightBits.val)
              (CShape.wordModulus signedWidth)
          have integerCongruence :=
            Int.natCast_modEq_iff.mpr naturalCongruence
          have productCongruence := leftRepresents.mul rightRepresents
          simpa only [Nat.cast_mul] using
            integerCongruence.trans productCongruence

private lemma rawSignedRepresents_sub {signedWidth : Nat}
    (left right : CShape.Word signedWidth) (leftValue rightValue : Int)
    (leftRepresents : RawSignedRepresents left leftValue)
    (rightRepresents : RawSignedRepresents right rightValue) :
    RawSignedRepresents
      (Resource.WordBinaryOpcode.eval .sub signedWidth
        (.product left right))
      (leftValue - rightValue) := by
  cases left with
  | unsignedWord leftBits =>
      cases right with
      | unsignedWord rightBits =>
          let modulus := CShape.wordModulus signedWidth
          change
            (leftBits.val : Int) ≡ leftValue [ZMOD (modulus : Int)]
            at leftRepresents
          change
            (rightBits.val : Int) ≡ rightValue [ZMOD (modulus : Int)]
            at rightRepresents
          change
            (((leftBits.val + modulus - rightBits.val) % modulus : Nat) : Int) ≡
                leftValue - rightValue
              [ZMOD (modulus : Int)]
          have rightLe : rightBits.val ≤ leftBits.val + modulus := by
            have rightLt : rightBits.val < modulus := rightBits.isLt
            omega
          have naturalCongruence :
              (leftBits.val + modulus - rightBits.val) % modulus ≡
                leftBits.val + modulus - rightBits.val [MOD modulus] :=
            Nat.mod_modEq (leftBits.val + modulus - rightBits.val) modulus
          have integerCongruence :=
            Int.natCast_modEq_iff.mpr naturalCongruence
          have arithmeticCongruence :
              (leftBits.val : Int) + (modulus : Int) -
                    (rightBits.val : Int) ≡
                leftValue - rightValue [ZMOD (modulus : Int)] := by
            simpa using
              (leftRepresents.add
                (Int.modulus_modEq_zero :
                  (modulus : Int) ≡ 0 [ZMOD (modulus : Int)])).sub
                rightRepresents
          have wrappedCongruence :
              ((leftBits.val + modulus - rightBits.val : Nat) : Int) ≡
                leftValue - rightValue [ZMOD (modulus : Int)] := by
            rw [Int.ofNat_sub rightLe, Nat.cast_add]
            exact arithmeticCongruence
          exact integerCongruence.trans wrappedCongruence

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
