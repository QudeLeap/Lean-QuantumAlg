/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Arithmetic

/-!
# Original candidate sign and strict range arithmetic

These pure bridges retain the original signed decoding interval and exponent
predicate. They are independent of storage layouts and executable classifiers.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- The strict candidate interval accepted by this one-slot machine. -/
def ExponentInRange (exponentBits : Nat) (value : Int) : Prop :=
  0 < value ∧ value < ((2 ^ exponentBits : Nat) : Int)

/-- The strict candidate interval is decidable. -/
instance exponentInRangeDecidable (exponentBits : Nat) (value : Int) :
    Decidable (ExponentInRange exponentBits value) := by
  unfold ExponentInRange
  infer_instance

/-- Exact unsigned readout gives the corresponding raw signed modular representation. -/
lemma rawSignedRepresents_of_toNat {width : Nat} (raw : CShape.Word width)
    (value : Nat) (rawValue : raw.toNat = value) :
    RawSignedRepresents raw (value : Int) := by
  unfold RawSignedRepresents Int.ModEq
  rw [rawValue]

/-- Decode a represented signed raw word into its sign Boolean and magnitude. -/
lemma rawSignedSignMagnitude {width : Nat} (widthPositive : 0 < width)
    (raw : CShape.Word width) (value : Int) (represented : RawSignedRepresents raw value)
    (range : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width value) :
    rawIsNegative raw = decide (value < 0) ∧ rawMagnitude raw = value.natAbs := by
  have decoded : decodeRawSignedWord raw = value :=
    rawSignedRepresents_decode_eq raw value widthPositive represented range
  by_cases negative : rawIsNegative raw = true
  · have valueEq : value = -(rawMagnitude raw : Int) := by
      calc
        value = decodeRawSignedWord raw := decoded.symm
        _ = -(rawMagnitude raw : Int) := by
          rw [SignedWord.RoundedDiv.decodeRawSignedWord_eq_signedMagnitude widthPositive raw,
            negative]
          simp only [if_pos True.intro]
    have magnitudePositive : 0 < rawMagnitude raw := by
      simpa only [rawMagnitude, CShape.wordModulus, negative, if_true] using
        (Nat.sub_pos_of_lt raw.toNat_lt)
    have magnitudePositiveInt : (0 : Int) < (rawMagnitude raw : Int) := by
      exact_mod_cast magnitudePositive
    have valueNegative : value < 0 := by
      rw [valueEq]
      omega
    have magnitudeInt : (rawMagnitude raw : Int) = (value.natAbs : Int) := by
      calc
        (rawMagnitude raw : Int) = -value := by rw [valueEq]; ring
        _ = (value.natAbs : Int) := by
          rw [Int.natCast_natAbs, abs_of_neg valueNegative]
    refine ⟨?_, ?_⟩
    · simp only [negative, valueNegative, decide_true]
    · exact_mod_cast magnitudeInt
  · have nonnegative : rawIsNegative raw = false :=
      Bool.eq_false_of_not_eq_true negative
    have valueEq : value = (rawMagnitude raw : Int) := by
      calc
        value = decodeRawSignedWord raw := decoded.symm
        _ = (rawMagnitude raw : Int) := by
          rw [SignedWord.RoundedDiv.decodeRawSignedWord_eq_signedMagnitude widthPositive raw,
            nonnegative]
          simp only [Bool.false_eq_true, if_false]
    have valueNonnegative : 0 ≤ value := by
      rw [valueEq]
      exact Int.natCast_nonneg _
    have magnitudeInt : (rawMagnitude raw : Int) = (value.natAbs : Int) := by
      calc
        (rawMagnitude raw : Int) = value := valueEq.symm
        _ = (value.natAbs : Int) := by
          rw [Int.natCast_natAbs, abs_of_nonneg valueNonnegative]
    refine ⟨?_, ?_⟩
    · have valueNotNegative : ¬ value < 0 := by omega
      simp only [nonnegative, valueNotNegative, decide_false]
    · exact_mod_cast magnitudeInt

/-- Boolean negation of a negative signed value is the nonnegative test. -/
lemma notNegativeBit (value : Int) :
    (!decide (value < 0)) = decide (0 ≤ value) := by
  by_cases negative : value < 0
  · have notNonnegative : ¬ 0 ≤ value := by omega
    simp [negative, notNonnegative]
  · have nonnegative : 0 ≤ value := by omega
    simp [negative, nonnegative]

/-- The literal three Boolean checks are exactly the strict signed range test. -/
lemma candidateRangeBit (exponentBits : Nat) (value : Int) :
    ((decide (value.natAbs ≠ 0) &&
      decide (value.natAbs < 2 ^ exponentBits)) &&
        decide (0 ≤ value)) =
      decide (ExponentInRange exponentBits value) := by
  unfold ExponentInRange
  by_cases negative : value < 0
  · have notNonnegative : ¬ 0 ≤ value := by omega
    have notPositive : ¬ 0 < value := by omega
    simp [notNonnegative, notPositive]
  · have nonnegative : 0 ≤ value := by omega
    by_cases zero : value = 0
    · subst value
      simp
    · have positive : 0 < value := by omega
      have magnitudeNonzero : value.natAbs ≠ 0 :=
        Nat.ne_of_gt (Int.natAbs_pos.mpr zero)
      have magnitudeBelow : value.natAbs < 2 ^ exponentBits ↔
          value < ((2 ^ exponentBits : Nat) : Int) := by
        constructor
        · intro bound
          have boundInt : (value.natAbs : Int) < ((2 ^ exponentBits : Nat) : Int) := by
            exact_mod_cast bound
          rw [Int.natAbs_of_nonneg nonnegative] at boundInt
          exact boundInt
        · intro bound
          have boundInt : (value.natAbs : Int) < ((2 ^ exponentBits : Nat) : Int) := by
            rw [Int.natAbs_of_nonneg nonnegative]
            exact bound
          exact_mod_cast boundInt
      simp [nonnegative, positive, magnitudeNonzero, magnitudeBelow]

/-- Boolean decoding commutes with the closed bit-negation opcode. -/
lemma bitNotEval_toBool (input : CShape.Value .bit) :
    (Resource.BitOpcode.eval .not input).toBool = !input.toBool := by
  cases input
  rfl

/-- Boolean decoding commutes with the closed bit-conjunction opcode. -/
lemma bitAndEval_toBool (left right : CShape.Value .bit) :
    (Resource.BitOpcode.eval .and (.product left right)).toBool =
      (left.toBool && right.toBool) := by
  cases left with
  | bit _ =>
      cases right with
      | bit _ => rfl


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
