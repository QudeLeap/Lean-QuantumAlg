/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correction.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Intermediate
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Correctness

/-! # Actual canonical modular doubling and complete clean-flag restoration -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

def doubledWord (target : Word) : Word :=
  ⟨(2 * target.val) % modulus,
    (Nat.mod_lt _ modulus_positive).trans modulus_lt_capacity⟩

lemma doubledWord_canonical (target : Word) : Canonical (doubledWord target) :=
  Nat.mod_lt _ modulus_positive

private lemma conditional_sum_word {Source : Type} {bound : Nat} (positive : 0 < bound)
    (source : Source) (word result : Fin bound) (selected : Bool) (amount : Nat)
    (numeric : (if selected then (word.val + amount) % bound else word.val) = result.val) :
    (if selected then
      ((source, (⟨(word.val + amount) % bound, Nat.mod_lt _ positive⟩ : Fin bound)), selected)
    else ((source, word), selected)) = ((source, result), selected) := by
  cases selected with
  | true =>
      simp only [↓reduceIte] at numeric ⊢
      exact congrArg (fun target : Fin bound => ((source, target), true)) (Fin.ext numeric)
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at numeric ⊢
      exact congrArg (fun target : Fin bound => ((source, target), false)) (Fin.ext numeric)

private lemma corrected_intermediate (source target : Word) (canonical : Canonical target) :
    let middle := intermediateWord target canonical
    let wrap := decide (modulus ≤ middle.val)
    sparseComplementStep ((source, middle), wrap) = ((source, doubledWord target), wrap) := by
  dsimp only
  have numeric := Nat.FixedWidth.NearPower.double_conditional_complement_eq_mod
    modulus_add_complement canonical
  have middleValue : (intermediateWord target canonical).val =
      Nat.FixedWidth.NearPower.doubleIntermediate modulus capacity target.val := rfl
  have resultValue : (doubledWord target).val = (2 * target.val) % modulus := rfl
  rw [← middleValue, ← resultValue] at numeric
  have scalar :
      (if decide (modulus ≤ (intermediateWord target canonical).val) then
        ((intermediateWord target canonical).val + complement) % capacity
      else (intermediateWord target canonical).val) = (doubledWord target).val := by
    simpa only [decide_eq_true_eq] using numeric
  exact (sparseComplementStep_eq_wordStep _).trans
    (conditional_sum_word (Nat.two_pow_pos width) source (intermediateWord target canonical)
      (doubledWord target) (decide (modulus ≤ (intermediateWord target canonical).val))
      complement scalar)

private lemma cleanup_iff_wrap (source target : Word) (canonical : Canonical target)
    (flag : Bool) :
    (targetLow.get ((source, doubledWord target), flag) = true ∧
      (doubledWord target).val < complement) ↔
        modulus ≤ (intermediateWord target canonical).val := by
  have arithmetic := Nat.FixedWidth.NearPower.double_cleanup_iff
    modulus_add_complement modulus_odd canonical
  rw [Nat.FixedWidth.NearPower.double_reduceOnce_eq_mod modulus_add_complement canonical]
    at arithmetic
  change (((2 * target.val) % modulus).testBit 0 = true ∧
    (2 * target.val) % modulus < complement) ↔ _
  rw [← Nat.mod_two_eq_one_iff_testBit_zero]
  exact arithmetic.symm

private lemma cleanup_from_wrap (source target : Word) (wrap : Bool)
    (condition : (targetLow.get ((source, target), wrap) = true ∧ target.val < complement) ↔
      wrap = true) :
    Cleanup.cleanupStep ((source, target), wrap) = ((source, target), false) := by
  have actual := Cleanup.doublingCleanup_step_eq ((source, target), wrap)
  have pure :
      (if targetLow.get ((source, target), wrap) = true ∧ target.val < complement then
        reductionBit.flip ((source, target), wrap) else ((source, target), wrap)) =
      ((source, target), false) := by
    cases wrap with
    | true =>
        rw [if_pos (condition.mpr rfl)]
        rfl
    | false =>
        rw [if_neg (fun selected => Bool.false_ne_true (condition.mp selected))]
        rfl
  exact actual.trans pure

private lemma proposition_iff_decide (selected : Prop) [Decidable selected] :
    selected ↔ decide selected = true := by
  simp only [decide_eq_true_eq]

/-- The complete native action doubles every canonical target, including zero,
and restores the entire arbitrary source word and the original clean flag. -/
lemma doubling_clean_canonical (source target : Word) (canonical : Canonical target) :
    doublingStep ((source, target), false) = ((source, doubledWord target), false) := by
  let middle := intermediateWord target canonical
  let wrap := decide (modulus ≤ middle.val)
  have carried : complementCarryStep ((source, middle), false) = ((source, middle), wrap) :=
    (carry_flag_step ((source, middle), false)).trans
      (congrArg (fun flag : Bool => ((source, middle), flag)) (Bool.false_xor wrap))
  have even : wrap = true → middle.val % 2 = 0 := by
    intro selected
    have wrapped : modulus ≤ middle.val := of_decide_eq_true selected
    exact Nat.FixedWidth.NearPower.doubleIntermediate_even_of_wrap canonical wrapped
  have corrected : Correction.correctionStep ((source, middle), wrap) =
      ((source, doubledWord target), wrap) :=
    (Correction.correctionStep_eq_sparseComplement _ even).trans
      (corrected_intermediate source target canonical)
  have condition :
      (targetLow.get ((source, doubledWord target), wrap) = true ∧
        (doubledWord target).val < complement) ↔ wrap = true :=
    (cleanup_iff_wrap source target canonical wrap).trans
      (proposition_iff_decide (modulus ≤ middle.val))
  have afterCarry :=
    (congrArg complementCarryStep (rotation_evenCorrection_clean source target canonical)).trans
      carried
  have afterCorrection := (congrArg Correction.correctionStep afterCarry).trans corrected
  exact (congrArg Cleanup.cleanupStep afterCorrection).trans
    (cleanup_from_wrap source (doubledWord target) wrap condition)

/-- The complete adjoint borrows any current source word while restoring a doubled value. -/
lemma inverseDoubling_doubledWord (source target : Word) (canonical : Canonical target) :
    stepList inverseDoublingGates ((source, doubledWord target), false) =
      ((source, target), false) := by
  have inverse := inverseDoubling_doubling ((source, target), false)
  exact (congrArg (stepList inverseDoublingGates)
    (doubling_clean_canonical source target canonical).symm).trans inverse

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
