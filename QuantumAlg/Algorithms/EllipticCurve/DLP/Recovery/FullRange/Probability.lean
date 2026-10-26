/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Kernel
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Tail

/-!
# Full-range ideal success mass with the zero character excluded

The observable is a union of strict left/right Fourier windows indexed by
nonzero cyclic characters.  Exact character-mixture probabilities permit a
separate lower bound in each component without counting overlapping observable
windows twice.  Excluding the zero character loses at most one over the order.
-/

namespace QuantumAlg.EllipticCurve.FullRange

open scoped BigOperators

noncomputable section

variable {order : Nat} [NeZero order]

/-- The strict two-phase event of one cyclic character, with the negative
right frequency required by recovery. -/
def characterWindow (width : Nat) (secret frequency : ZMod order) (raw : Branch width) : Prop :=
  qpePhaseDistance width ((frequency.val : ℝ) / order) raw.1 < 1 / (2 * order) ∧
    qpePhaseDistance width (((-secret * frequency).val : ℝ) / order) raw.2 < 1 / (2 * order)

/-- The observable union of all nonzero-character strict windows. -/
def recoverableWindow (width : Nat) (secret : ZMod order) (raw : Branch width) : Prop :=
  ∃ frequency : ZMod order, frequency ≠ 0 ∧ characterWindow width secret frequency raw

/-- One character component's actual geometric mass on an arbitrary observable. -/
def characterEventMass (width : Nat) (secret frequency : ZMod order)
    (event : Branch width → Prop) : ℝ := by
  classical
  exact ∑ raw : Branch width, if event raw then
    ‖phaseRegisterGeometricAmplitude width ((frequency.val : ℝ) / order) raw.1‖ ^ 2 *
      ‖phaseRegisterGeometricAmplitude width (((-secret * frequency).val : ℝ) / order) raw.2‖ ^ 2
    else 0

omit [NeZero order] in
lemma characterEventMass_nonneg (width : Nat) (secret frequency : ZMod order)
    (event : Branch width → Prop) : 0 ≤ characterEventMass width secret frequency event := by
  classical
  apply Finset.sum_nonneg
  intro raw _
  split_ifs <;> positivity

omit [NeZero order] in
lemma characterEventMass_mono (width : Nat) (secret frequency : ZMod order)
    (first second : Branch width → Prop) (subset : ∀ raw, first raw → second raw) :
    characterEventMass width secret frequency first ≤
      characterEventMass width secret frequency second := by
  classical
  apply Finset.sum_le_sum
  intro raw _
  by_cases inside : first raw
  · simp only [if_pos inside, if_pos (subset raw inside)]
    exact le_rfl
  · simp only [if_neg inside]
    split_ifs <;> positivity

omit [NeZero order] in
/-- The two independent full-grid character factors give precisely the product
of their strict-window masses. -/
lemma characterWindow_mass_eq (width : Nat) (secret frequency : ZMod order) :
    characterEventMass width secret frequency (characterWindow width secret frequency) =
      strictWindowMass width ((frequency.val : ℝ) / order) (1 / (2 * order)) *
        strictWindowMass width (((-secret * frequency).val : ℝ) / order) (1 / (2 * order)) := by
  classical
  unfold characterEventMass strictWindowMass
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  dsimp only [characterWindow]
  by_cases leftGood : qpePhaseDistance width ((frequency.val : ℝ) / order) left <
      1 / (2 * order)
  · by_cases rightGood :
        qpePhaseDistance width (((-secret * frequency).val : ℝ) / order) right <
          1 / (2 * order)
    · simp only [leftGood, rightGood, and_self, if_true]
    · simp only [leftGood, rightGood, and_false, if_true, if_false, mul_zero]
  · simp only [leftGood, false_and, if_false, zero_mul]

/-- Full ideal Born mass of the observable nonzero-character window union. -/
def idealRecoverableMass (width : Nat) (seed secret : ZMod order) : ℝ := by
  classical
  exact ∑ raw : Branch width, if recoverableWindow width secret raw then
    ∑ output : ZMod order, ‖idealKernel width seed secret raw.1 raw.2 output‖ ^ 2 else 0

/-- The observable's probability is exactly its character mixture, even when
the observable is a union with overlapping windows. -/
lemma idealRecoverableMass_eq_mixture (width : Nat) (seed secret : ZMod order) :
    idealRecoverableMass width seed secret =
      (order : ℝ)⁻¹ * ∑ frequency : ZMod order,
        characterEventMass width secret frequency (recoverableWindow width secret) := by
  classical
  unfold idealRecoverableMass characterEventMass
  calc
    _ = ∑ raw : Branch width, (order : ℝ)⁻¹ * ∑ frequency : ZMod order,
        if recoverableWindow width secret raw then
          ‖phaseRegisterGeometricAmplitude width ((frequency.val : ℝ) / order) raw.1‖ ^ 2 *
            ‖phaseRegisterGeometricAmplitude width
              (((-secret * frequency).val : ℝ) / order) raw.2‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro raw _
      by_cases accepted : recoverableWindow width secret raw
      · simpa only [if_pos accepted] using
          idealKernel_square_sum_eq_mixture width seed secret raw.1 raw.2
      · simp only [if_neg accepted, Finset.sum_const_zero, mul_zero]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- The exact ideal full-range distribution retains 55/64 minus at most one
over the subgroup order after excluding the zero character. -/
lemma idealRecoverableMass_ge (width : Nat) (seed secret : ZMod order)
    (oversampling : 16 * order ≤ 2 ^ width) :
    (55 : ℝ) / 64 - 1 / order ≤ idealRecoverableMass width seed secret := by
  classical
  have orderPositive : 0 < order := Nat.pos_of_ne_zero (NeZero.ne order)
  have orderPositiveReal : (0 : ℝ) < order := by exact_mod_cast orderPositive
  let nonzero := (Finset.univ : Finset (ZMod order)).erase 0
  have nonzeroCard : nonzero.card = order - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have component (frequency : ZMod order) (member : frequency ∈ nonzero) :
      (55 : ℝ) / 64 ≤
        characterEventMass width secret frequency (recoverableWindow width secret) := by
    have nonzeroFrequency := (Finset.mem_erase.mp member).1
    have windows := twoPhase_strictWindowMass_ge width order orderPositive oversampling
      ((frequency.val : ℝ) / order) (((-secret * frequency).val : ℝ) / order)
    rw [← characterWindow_mass_eq] at windows
    exact windows.trans (characterEventMass_mono width secret frequency _ _
      (fun _ inside => ⟨frequency, nonzeroFrequency, inside⟩))
  have sumBound : ((order - 1 : Nat) : ℝ) * (55 / 64) ≤
      ∑ frequency : ZMod order,
        characterEventMass width secret frequency (recoverableWindow width secret) := by
    calc
      _ = ∑ _frequency ∈ nonzero, (55 : ℝ) / 64 := by simp [nonzeroCard]
      _ ≤ ∑ frequency ∈ nonzero,
          characterEventMass width secret frequency (recoverableWindow width secret) :=
        Finset.sum_le_sum fun frequency member => component frequency member
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun frequency _ _ => characterEventMass_nonneg width secret frequency _)
  rw [idealRecoverableMass_eq_mixture]
  have massBound := mul_le_mul_of_nonneg_left sumBound (inv_nonneg.mpr orderPositiveReal.le)
  apply le_trans _ massBound
  rw [Nat.cast_sub (by omega : 1 ≤ order), Nat.cast_one]
  have identity : (order : ℝ)⁻¹ * ((order : ℝ) - 1) * (55 / 64) =
      55 / 64 - (55 / 64) / order := by field_simp
  rw [← mul_assoc, identity]
  have reserve : (55 / 64 : ℝ) / order ≤ 1 / order :=
    div_le_div_of_nonneg_right (by norm_num) orderPositiveReal.le
  linarith

end

end QuantumAlg.EllipticCurve.FullRange
