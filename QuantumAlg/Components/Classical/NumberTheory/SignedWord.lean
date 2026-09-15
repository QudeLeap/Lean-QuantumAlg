/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Util.Classical.NumberTheory.Extended

/-!
# Raw two's-complement word arithmetic

These representation lemmas describe the existing Core word instructions
modulo the word width. Exact signed decoding additionally requires the
signed interval bound. Executable clients apply the same instructions to
actual storage through `Circuit`.
-/

section

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord

open ClassicalAlgorithms
open ClassicalAlgorithms.NumberTheory
open ClassicalAlgorithms.Modular

/-- A raw word represents an integer modulo its two's-complement modulus. -/
def RawSignedRepresents {signedWidth : Nat}
    (encoded : CShape.Word signedWidth) (value : Int) : Prop :=
  Int.ModEq (CShape.wordModulus signedWidth : Int)
    (encoded.toNat : Int) value

/-- A nonnegative raw representation below the word modulus has its natural value. -/
theorem rawSignedRepresents_toNat_eq_of_lt {width value : Nat}
    (encoded : CShape.Word width)
    (represents : RawSignedRepresents encoded (value : Int))
    (valueFits : value < CShape.wordModulus width) :
    encoded.toNat = value := by
  unfold RawSignedRepresents at represents
  have congruence : encoded.toNat ≡ value [MOD CShape.wordModulus width] :=
    Int.natCast_modEq_iff.mp represents
  exact congruence.eq_of_lt_of_lt encoded.toNat_lt valueFits

/-- The canonical low-word encoding of an integer represents that integer. -/
theorem rawSignedWordRepresents_ofInt (signedWidth : Nat) (value : Int) :
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

/-- Decode one raw fixed-width word with the canonical two's-complement decoder. -/
def decodeRawSignedWord {signedWidth : Nat}
    (encoded : CShape.Word signedWidth) : Int :=
  (BoundedSigned.decode (decodeWord encoded)).toInt

/-- A modulo-represented integer in the signed interval decodes exactly. -/
theorem rawSignedRepresents_decode_eq {signedWidth : Nat}
    (encoded : CShape.Word signedWidth) (value : Int)
    (widthPositive : 0 < signedWidth)
    (represents : RawSignedRepresents encoded value)
    (range :
      ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
        signedWidth value) :
    decodeRawSignedWord encoded = value := by
  cases encoded with
  | unsignedWord bits =>
      change (BoundedSigned.decode bits).toInt = value
      change
        (bits.val : Int) ≡ value
          [ZMOD (CShape.wordModulus signedWidth : Int)]
        at represents
      have canonical := rawSignedWordRepresents_ofInt signedWidth value
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

/-- A literal word copy preserves every raw two's-complement representation. -/
theorem rawSignedWordRepresents_copy {signedWidth : Nat}
    (input : CShape.Word signedWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .copy signedWidth input) value := by
  simpa only [Resource.WordUnaryOpcode.eval] using represents

/-- Resizing represents the source word's raw unsigned value at the target width. -/
theorem rawSignedWordRepresents_wordResize
    {sourceWidth targetWidth : Nat} (input : CShape.Word sourceWidth) :
    RawSignedRepresents (CShape.wordResize targetWidth input)
      (input.toNat : Int) := by
  cases input with
  | unsignedWord bits =>
      change
        ((bits.val % CShape.wordModulus targetWidth : Nat) : Int) ≡
            (bits.val : Int)
          [ZMOD (CShape.wordModulus targetWidth : Int)]
      have naturalCongruence :
          bits.val % CShape.wordModulus targetWidth ≡ bits.val
            [MOD CShape.wordModulus targetWidth] :=
        Nat.mod_modEq bits.val (CShape.wordModulus targetWidth)
      exact Int.natCast_modEq_iff.mpr naturalCongruence

/-- Truncating to a no-wider word preserves the represented integer. -/
theorem rawSignedWordRepresents_resize_of_width_le
    {sourceWidth targetWidth : Nat} (widthLe : targetWidth ≤ sourceWidth)
    (input : CShape.Word sourceWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents (CShape.wordResize targetWidth input) value := by
  have resized := rawSignedWordRepresents_wordResize
    (targetWidth := targetWidth) input
  unfold RawSignedRepresents at resized represents ⊢
  have modulusDvd :
      (CShape.wordModulus targetWidth : Int) ∣
        (CShape.wordModulus sourceWidth : Int) := by
    exact Int.natCast_dvd_natCast.mpr (by
      simpa [CShape.wordModulus] using pow_dvd_pow 2 widthLe)
  exact resized.trans (represents.of_dvd modulusDvd)

/-- No-wider resizing is the target-width two's-complement encoding. -/
theorem rawResize_eq_ofInt_of_rawSignedRepresents
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
        rawSignedWordRepresents_ofInt targetWidth value
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

/-- Incrementing a raw word represents addition by one modulo its width. -/
theorem rawSignedWordRepresents_increment {signedWidth : Nat}
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

/-- Low-word multiplication preserves the product modulo the shared width. -/
theorem rawSignedWordRepresents_mulLow {signedWidth : Nat}
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

/-- Wrapping subtraction preserves the integer difference modulo the width. -/
theorem rawSignedWordRepresents_sub {signedWidth : Nat}
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

/-- A literal low word represents its source natural number modulo its width. -/
theorem rawSignedWordRepresents_wordOfNat (signedWidth value : Nat) :
    RawSignedRepresents (CShape.wordOfNat signedWidth value) (value : Int) := by
  change
    ((value % CShape.wordModulus signedWidth : Nat) : Int) ≡
        (value : Int)
      [ZMOD (CShape.wordModulus signedWidth : Int)]
  exact Int.natCast_modEq_iff.mpr
    (Nat.mod_modEq value (CShape.wordModulus signedWidth))

/-- Complementing a raw word represents negation followed by subtraction of one. -/
theorem rawSignedWordRepresents_complement {signedWidth : Nat}
    (input : CShape.Word signedWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .complement signedWidth input)
      (-value - 1) := by
  cases input with
  | unsignedWord bits =>
      let modulus := CShape.wordModulus signedWidth
      change
        (bits.val : Int) ≡ value [ZMOD (modulus : Int)]
        at represents
      change
        (((modulus - 1 - bits.val) % modulus : Nat) : Int) ≡
            -value - 1
          [ZMOD (modulus : Int)]
      have bitsLe : bits.val ≤ modulus - 1 := by
        have bitsLt : bits.val < modulus := bits.isLt
        omega
      have modulusPositive : 0 < modulus := by
        exact CShape.wordModulus_pos signedWidth
      have oneLe : 1 ≤ modulus := by
        omega
      have naturalCongruence :
          (modulus - 1 - bits.val) % modulus ≡ modulus - 1 - bits.val
            [MOD modulus] :=
        Nat.mod_modEq (modulus - 1 - bits.val) modulus
      have integerCongruence := Int.natCast_modEq_iff.mpr naturalCongruence
      have arithmeticCongruence :
          (modulus : Int) - 1 - (bits.val : Int) ≡ -value - 1
            [ZMOD (modulus : Int)] := by
        have modulusMinusOne :
            (modulus : Int) - 1 ≡ -1 [ZMOD (modulus : Int)] := by
          simpa using
            (Int.modulus_modEq_zero :
              (modulus : Int) ≡ 0 [ZMOD (modulus : Int)]).sub
              (Int.ModEq.refl 1)
        convert modulusMinusOne.sub represents using 1; ring
      have wrappedCongruence :
          ((modulus - 1 - bits.val : Nat) : Int) ≡ -value - 1
            [ZMOD (modulus : Int)] := by
        rw [Int.ofNat_sub bitsLe, Int.ofNat_sub oneLe, Nat.cast_one]
        exact arithmeticCongruence
      exact integerCongruence.trans wrappedCongruence

/-- Decrementing a raw word represents subtraction of one modulo its width. -/
theorem rawSignedWordRepresents_decrement {signedWidth : Nat}
    (input : CShape.Word signedWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .decrement signedWidth input)
      (value - 1) := by
  simpa only [Resource.WordUnaryOpcode.eval, Resource.WordBinaryOpcode.eval] using
    rawSignedWordRepresents_sub input (CShape.wordOfNat signedWidth 1) value 1
      represents (rawSignedWordRepresents_wordOfNat signedWidth 1)

/-- Wrapping addition preserves the signed integer sum modulo the shared width. -/
theorem rawSignedWordRepresents_add {signedWidth : Nat}
    (left right : CShape.Word signedWidth) (leftValue rightValue : Int)
    (leftRepresents : RawSignedRepresents left leftValue)
    (rightRepresents : RawSignedRepresents right rightValue) :
    RawSignedRepresents
      (Resource.WordBinaryOpcode.eval .add signedWidth (.product left right))
      (leftValue + rightValue) := by
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
            (((leftBits.val + rightBits.val) %
                  CShape.wordModulus signedWidth : Nat) : Int) ≡
                leftValue + rightValue
              [ZMOD (CShape.wordModulus signedWidth : Int)]
          have naturalCongruence :
              (leftBits.val + rightBits.val) %
                    CShape.wordModulus signedWidth ≡
                  leftBits.val + rightBits.val
                [MOD CShape.wordModulus signedWidth] :=
            Nat.mod_modEq (leftBits.val + rightBits.val)
              (CShape.wordModulus signedWidth)
          have integerCongruence :=
            Int.natCast_modEq_iff.mpr naturalCongruence
          have sumCongruence := leftRepresents.add rightRepresents
          simpa only [Nat.cast_add] using
            integerCongruence.trans sumCongruence

/-- A one-bit raw left shift represents multiplication by two modulo the width. -/
theorem rawSignedWordRepresents_shiftLeft {signedWidth : Nat}
    (input : CShape.Word signedWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .shiftLeft signedWidth input)
      (2 * value) := by
  cases input with
  | unsignedWord bits =>
      change
        (bits.val : Int) ≡ value
          [ZMOD (CShape.wordModulus signedWidth : Int)]
        at represents
      change
        (((2 * bits.val) % CShape.wordModulus signedWidth : Nat) : Int) ≡
            2 * value
          [ZMOD (CShape.wordModulus signedWidth : Int)]
      have naturalCongruence :
          (2 * bits.val) % CShape.wordModulus signedWidth ≡ 2 * bits.val
            [MOD CShape.wordModulus signedWidth] :=
        Nat.mod_modEq (2 * bits.val) (CShape.wordModulus signedWidth)
      have integerCongruence := Int.natCast_modEq_iff.mpr naturalCongruence
      have doubledCongruence := (Int.ModEq.refl (2 : Int)).mul represents
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        integerCongruence.trans doubledCongruence

/-- Complement followed by increment represents raw two's-complement negation. -/
theorem rawSignedWordRepresents_negate {signedWidth : Nat}
    (input : CShape.Word signedWidth) (value : Int)
    (represents : RawSignedRepresents input value) :
    RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .increment signedWidth
        (Resource.WordUnaryOpcode.eval .complement signedWidth input))
      (-value) := by
  have incremented := rawSignedWordRepresents_increment
    (Resource.WordUnaryOpcode.eval .complement signedWidth input)
    (-value - 1) (rawSignedWordRepresents_complement input value represents)
  convert incremented using 1; ring

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord

end
