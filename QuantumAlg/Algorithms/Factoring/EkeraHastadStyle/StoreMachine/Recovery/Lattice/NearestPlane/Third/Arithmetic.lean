/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Arithmetic

/-!
# Integer contracts of third-coordinate sign normalization

The decoded signed range identifies the original integer's sign and magnitude.
Changing both numerator and denominator signs preserves the rounded coefficient.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- The actual raw sign equals the sign of any represented integer in the signed range. -/
theorem raw_sign_of_represents {width : Nat} (raw : CShape.Word width) (value : Int)
    (positive : 0 < width) (represents : RawSignedRepresents raw value)
    (range : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width value) :
    rawIsNegative raw = decide (value < 0) := by
  have decoded := rawSignedRepresents_decode_eq raw value positive represents range
  rw [RoundedDiv.decodeRawSignedWord_eq_signedMagnitude positive] at decoded
  cases sign : rawIsNegative raw with
  | false =>
    simp only [sign, Bool.false_eq_true, if_false] at decoded
    have nonnegative : 0 ≤ value := by omega
    simp [not_lt_of_ge nonnegative]
  | true =>
    simp only [sign, if_true] at decoded
    have magnitudePositive : 0 < rawMagnitude raw := by
      simp only [rawMagnitude, sign, if_true]
      exact Nat.sub_pos_of_lt raw.toNat_lt
    have negative : value < 0 := by omega
    simp [negative]

/-- The actual raw magnitude equals the absolute value of the represented in-range integer. -/
theorem raw_magnitude_of_represents {width : Nat} (raw : CShape.Word width) (value : Int)
    (positive : 0 < width) (represents : RawSignedRepresents raw value)
    (range : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width value) :
    rawMagnitude raw = value.natAbs := by
  have decoded := rawSignedRepresents_decode_eq raw value positive represents range
  rw [RoundedDiv.decodeRawSignedWord_eq_signedMagnitude positive] at decoded
  cases sign : rawIsNegative raw with
  | false =>
    simp only [sign, Bool.false_eq_true, if_false] at decoded
    rw [← decoded]
    exact (Int.natAbs_natCast _).symm
  | true =>
    simp only [sign, if_true] at decoded
    rw [← decoded, Int.natAbs_neg, Int.natAbs_natCast]

/-- Simultaneously normalizing both signs preserves the original rounded coefficient. -/
theorem nearestIntegerCoefficient_sign_normalize_denominator
    (numerator denominator : Int) :
    NumberTheory.nearestIntegerCoefficient
      (if denominator < 0 then -numerator else numerator)
      (denominator.natAbs : Int) =
      NumberTheory.nearestIntegerCoefficient numerator denominator := by
  by_cases denominatorNegative : denominator < 0
  · have magnitude : (denominator.natAbs : Int) = -denominator := by
      simp only [Int.natCast_natAbs, abs_of_neg denominatorNegative]
    rw [if_pos denominatorNegative, magnitude]
    simp only [NumberTheory.nearestIntegerCoefficient, Int.cast_neg, neg_div_neg_eq]
  · have denominatorNonnegative : 0 ≤ denominator := le_of_not_gt denominatorNegative
    have magnitude : (denominator.natAbs : Int) = denominator := by
      simp only [Int.natCast_natAbs, abs_of_nonneg denominatorNonnegative]
    rw [if_neg denominatorNegative, magnitude]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
