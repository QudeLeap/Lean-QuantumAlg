/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification.Values
import all QuantumAlg.Util.NumberTheory.LatticeReduction

/-!
# Integer formulas for signed nearest division

These exact formulas retain nearest-integer rounding and its negative tie
correction. Width bounds justify the native word operations independently
of the circuit assembled by the executable owner.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

/-- The positive raw branch uses the imported unsigned nearest-integer formula. -/
theorem nearestIntegerCoefficient_ofNat_formula
    (numerator denominator : Nat) (positive : 0 < denominator) :
    QuantumAlg.NumberTheory.nearestIntegerCoefficient (numerator : Int)
        (denominator : Int) =
      (((2 * numerator + denominator) / (2 * denominator) : Nat) : Int) := by
  exact QuantumAlg.NumberTheory.nearestIntegerCoefficient_ofNat
    numerator denominator positive

/-- The negative raw branch uses the imported predecessor-corrected formula. -/
theorem nearestIntegerCoefficient_neg_ofNat_formula
    (magnitude denominator : Nat) (magnitudePositive : 0 < magnitude)
    (denominatorPositive : 0 < denominator) :
    QuantumAlg.NumberTheory.nearestIntegerCoefficient (-(magnitude : Int))
        (denominator : Int) =
      -(((2 * magnitude + denominator - 1) / (2 * denominator) : Nat) : Int) := by
  exact QuantumAlg.NumberTheory.nearestIntegerCoefficient_neg_ofNat magnitude denominator
    magnitudePositive denominatorPositive

/-- At positive width the word modulus splits into two sign thresholds. -/
theorem wordModulus_split {width : Nat} (widthPositive : 0 < width) :
    CShape.wordModulus width = 2 * 2 ^ (width - 1) := by
  simp only [CShape.wordModulus]
  calc
    2 ^ width = 2 ^ (width - 1 + 1) := by
      congr 1
      omega
    _ = 2 ^ (width - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (width - 1) := Nat.mul_comm _ _

/-- Every raw word fits strictly into the next wider word. -/
theorem wordModulus_lt_succ (width : Nat) :
    CShape.wordModulus width < CShape.wordModulus (width + 1) := by
  simp only [CShape.wordModulus, pow_succ]
  have positive : 0 < 2 ^ width := Nat.two_pow_pos _
  omega

/-- The next wider word has twice the modulus of the source word. -/
theorem wordModulus_succ (width : Nat) :
    CShape.wordModulus (width + 1) = 2 * CShape.wordModulus width := by
  simp only [CShape.wordModulus, pow_succ]
  exact Nat.mul_comm _ _

/-- The selected unsigned magnitude always fits its source raw word width. -/
theorem rawMagnitude_lt_wordModulus {width : Nat}
    (raw : CShape.Word width) :
    rawMagnitude raw < CShape.wordModulus width := by
  by_cases negative : rawIsNegative raw = true
  · simpa only [rawMagnitude, negative, if_true] using
      (Nat.sub_lt (CShape.wordModulus_pos width)
        (rawIsNegative_true_toNat_pos raw negative))
  · have nonnegative : rawIsNegative raw = false :=
      Bool.eq_false_of_not_eq_true negative
    rw [CShape.wordModulus]
    simp only [rawMagnitude, nonnegative, Bool.false_eq_true, if_false]
    simpa only [CShape.wordModulus] using raw.toNat_lt

/-- The generic raw decoder agrees with the sign and magnitude used by this body. -/
theorem decodeRawSignedWord_eq_signedMagnitude {width : Nat}
    (widthPositive : 0 < width) (raw : CShape.Word width) :
    decodeRawSignedWord raw =
      if rawIsNegative raw then
        -(rawMagnitude raw : Int)
      else
        (rawMagnitude raw : Int) := by
  change (BitVec.ofFin (decodeWord raw)).toInt = _
  rw [BitVec.toInt_eq_toNat_cond]
  have decodedValue : (decodeWord raw).val = raw.toNat := by
    cases raw
    rfl
  simp only [BitVec.toNat_ofFin, decodedValue]
  have powerSplit := wordModulus_split widthPositive
  by_cases negative : rawIsNegative raw = true
  · have threshold : 2 ^ (width - 1) ≤ raw.toNat := by
      unfold rawIsNegative at negative
      exact of_decide_eq_true negative
    have notSmall : ¬ 2 * raw.toNat < 2 ^ width := by
      simp only [CShape.wordModulus] at powerSplit
      omega
    rw [if_neg notSmall]
    simp only [rawMagnitude, negative, if_true, CShape.wordModulus]
    have rawLe : raw.toNat ≤ 2 ^ width := Nat.le_of_lt raw.toNat_lt
    rw [Int.ofNat_sub rawLe]
    ring
  · have nonnegative : rawIsNegative raw = false :=
      Bool.eq_false_of_not_eq_true negative
    have notThreshold : ¬ 2 ^ (width - 1) ≤ raw.toNat := by
      intro threshold
      apply negative
      unfold rawIsNegative
      exact decide_eq_true threshold
    have belowThreshold : raw.toNat < 2 ^ (width - 1) :=
      Nat.lt_of_not_ge notThreshold
    have small : 2 * raw.toNat < 2 ^ width := by
      simp only [CShape.wordModulus] at powerSplit
      omega
    rw [if_pos small]
    simp [rawMagnitude, nonnegative]

/-- A positive-width signed magnitude is at most half of the raw modulus. -/
theorem rawMagnitude_twice_le {width : Nat} (positive : 0 < width)
    (raw : CShape.Word width) : 2 * rawMagnitude raw ≤ CShape.wordModulus width := by
  have split := wordModulus_split positive
  by_cases negative : rawIsNegative raw = true
  · have high : 2 ^ (width - 1) ≤ raw.toNat := of_decide_eq_true negative
    simp only [rawMagnitude, negative, if_true]
    omega
  · have low : raw.toNat < 2 ^ (width - 1) := by
      have absent : ¬ 2 ^ (width - 1) ≤ raw.toNat := by
        simpa only [rawIsNegative, decide_eq_true_eq] using negative
      omega
    have flag : rawIsNegative raw = false := Bool.eq_false_of_not_eq_true negative
    simp only [rawMagnitude, flag, Bool.false_eq_true, if_false]
    omega

/-- The uncorrected doubled-magnitude dividend fits the actual one-bit-wider word. -/
theorem roundedDividend_fits {width : Nat} (positive : 0 < width)
    (raw denominator : CShape.Word width) :
    2 * rawMagnitude raw + denominator.toNat < CShape.wordModulus (width + 1) := by
  have magnitudeBound := rawMagnitude_twice_le positive raw
  have denominatorBound : denominator.toNat < CShape.wordModulus width := denominator.toNat_lt
  rw [wordModulus_succ]
  omega

/-- Doubling an unsigned denominator is exact in the one-bit-wider word. -/
theorem doubledDenominator_fits {width : Nat} (denominator : CShape.Word width) :
    2 * denominator.toNat < CShape.wordModulus (width + 1) := by
  have bounded : denominator.toNat < CShape.wordModulus width := denominator.toNat_lt
  rw [wordModulus_succ]
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
