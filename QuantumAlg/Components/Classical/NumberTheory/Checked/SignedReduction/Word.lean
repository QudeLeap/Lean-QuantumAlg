/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Model

/-!
# Original fixed-width signed-reduction bridges

The original sign-threshold and two's-complement magnitude arithmetic is
independent of machine execution. Existing names and proof bodies are
preserved, including the positive-width and nonzero-input conditions used
only inside the actual lexical signed-reduction implementation.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction

open ClassicalAlgorithms ClassicalAlgorithms.NumberTheory ClassicalAlgorithms.Modular

/-- Boolean decoding commutes with the closed bit-negation opcode. -/
lemma bitNotEval_toBool (input : CShape.Value .bit) :
    (Resource.BitOpcode.not.eval input).toBool = !input.toBool := by
  cases input
  rfl

/-- Complementing a zero word produces the largest word of the same width. -/
lemma wordComplement_zero_toNat {width : Nat} (input : CShape.Word width)
    (inputZero : input.toNat = 0) :
    (CShape.wordComplement width input).toNat =
      CShape.wordModulus width - 1 := by
  have modulusPositive := CShape.wordModulus_pos width
  simp only [CShape.wordComplement, CShape.wordOfNat_val, inputZero,
    Nat.sub_zero]
  rw [Nat.mod_eq_of_lt]
  omega

/-- Shifting the largest positive-width word right produces the word just
below the sign threshold. -/
lemma wordShiftRight_fullMinusOne_toNat {width : Nat}
    (widthPositive : 0 < width) (input : CShape.Word width)
    (inputValue : input.toNat = CShape.wordModulus width - 1) :
    (CShape.wordShiftRight width input).toNat =
      2 ^ (width - 1) - 1 := by
  have halfPositive : 0 < 2 ^ (width - 1) := Nat.two_pow_pos _
  have powerSplit :
      CShape.wordModulus width = 2 * 2 ^ (width - 1) := by
    simp only [CShape.wordModulus]
    calc
      2 ^ width = 2 ^ (width - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (width - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (width - 1) := Nat.mul_comm _ _
  simp only [CShape.wordShiftRight, CShape.wordOfNat_val, inputValue]
  rw [Nat.mod_eq_of_lt]
  · omega
  · have inputRange : input.toNat < CShape.wordModulus width :=
      input.toNat_lt
    omega

/-- Incrementing the word immediately below the sign threshold produces the
threshold exactly, without fixed-width wraparound. -/
lemma wordIncrement_belowThreshold_toNat {width : Nat}
    (widthPositive : 0 < width) (input : CShape.Word width)
    (inputValue : input.toNat = 2 ^ (width - 1) - 1) :
    (Resource.WordUnaryOpcode.eval .increment width input).toNat =
      2 ^ (width - 1) := by
  have halfPositive : 0 < 2 ^ (width - 1) := Nat.two_pow_pos _
  have powerSplit :
      CShape.wordModulus width = 2 * 2 ^ (width - 1) := by
    simp only [CShape.wordModulus]
    calc
      2 ^ width = 2 ^ (width - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (width - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (width - 1) := Nat.mul_comm _ _
  simp only [Resource.WordUnaryOpcode.eval, CShape.wordOfNat_val, inputValue]
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

/-- Fixed-width complement followed by increment realizes unsigned
two's-complement magnitude for every nonzero input. -/
lemma complementIncrement_toNat {width : Nat} (input : CShape.Word width)
    (inputPositive : 0 < input.toNat) :
    (Resource.WordUnaryOpcode.eval .increment width
      (Resource.WordUnaryOpcode.eval .complement width input)).toNat =
        CShape.wordModulus width - input.toNat := by
  have inputRange : input.toNat < CShape.wordModulus width :=
    input.toNat_lt
  have complementRange :
      CShape.wordModulus width - 1 - input.toNat <
        CShape.wordModulus width := by
    omega
  have resultRange :
      CShape.wordModulus width - input.toNat <
        CShape.wordModulus width := by
    omega
  simp only [Resource.WordUnaryOpcode.eval, CShape.wordComplement,
    CShape.wordOfNat_val]
  rw [Nat.mod_eq_of_lt complementRange]
  have numeratorEq :
      CShape.wordModulus width - 1 - input.toNat + 1 =
        CShape.wordModulus width - input.toNat := by
    omega
  rw [numeratorEq, Nat.mod_eq_of_lt resultRange]

/-- A raw word classified as negative is necessarily nonzero. -/
lemma rawIsNegative_true_toNat_pos {width : Nat}
    (raw : CShape.Word (signedWidth width))
    (negative : rawIsNegative raw = true) :
    0 < raw.toNat := by
  have thresholdPositive : 0 < 2 ^ (signedWidth width - 1) :=
    Nat.two_pow_pos _
  have thresholdLe : 2 ^ (signedWidth width - 1) ≤ raw.toNat := by
    unfold rawIsNegative at negative
    exact of_decide_eq_true negative
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction
