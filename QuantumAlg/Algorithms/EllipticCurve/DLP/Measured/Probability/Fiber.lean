/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Ideal
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber

/-!
# Original Fourier amplitudes on the finite image of group outputs

The original range preparation and inverse Fourier circuit give exactly the
source fiber sum at each selected full-group label. Padding contributes zero.
The seed cancels only in proofs of label equality; the mathematical labels
themselves retain the actual group value. The secret is solely a witness used
to identify useful frequencies, with the original known order and oversampling.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open FiniteCyclicDLP ConcreteCircuitAccess Canonical.Probability
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Include an original source-range exponent in its unchanged Fourier register. -/
def sourceFourierIndex {G : Type} [Group G] (problem : KnownOrderProblem G)
    (value : Fin problem.order) : Fin (2 ^ orderWidth problem) :=
  ⟨value.val, value.isLt.trans_le (order_le_fourierModulus problem)⟩

/-- The actual pair of inverse Fourier circuits has the original two source phases. -/
theorem exponentReadout_pair_entry {G : Type} [Group G]
    (problem : KnownOrderProblem G)
    (frequency branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) :
    (exponentReadoutCircuit problem).binaryMatrix (prodEquiv frequency) (prodEquiv branch) =
      star (invSqrtN (orderWidth problem) *
        ω (orderWidth problem) ^ (branch.1.val * frequency.1.val)) *
      star (invSqrtN (orderWidth problem) *
        ω (orderWidth problem) ^ (branch.2.val * frequency.2.val)) := by
  rw [exponentReadoutCircuit_binaryMatrix, UnitaryOperator.tensor_apply]
  simp only [Equiv.symm_apply_apply]
  change star (QFTOperator (orderWidth problem) branch.1 frequency.1) *
    star (QFTOperator (orderWidth problem) branch.2 frequency.2) = _
  simp only [QFTOperator_entry]

/-- Each original in-range prepared branch contributes precisely the source fiber term. -/
theorem preparedReadout_fiberTerm {G : Type} [Group G]
    (problem : KnownOrderProblem G) (input : SecretInput problem)
    (frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (tail right : Fin problem.order) :
    (exponentReadoutCircuit problem).binaryMatrix (prodEquiv frequency)
        (prodEquiv (sourceFourierIndex problem (fiberLeft problem input tail right),
          sourceFourierIndex problem right)) *
      preparedBranchAmplitude problem
        (sourceFourierIndex problem (fiberLeft problem input tail right),
          sourceFourierIndex problem right) =
      selectedFiberTerm input frequency.1 frequency.2 tail right := by
  rw [exponentReadout_pair_entry]
  simp only [preparedBranchAmplitude, Concrete.BornBridge.exponentState_apply,
    sourceFourierIndex, Fin.isLt, if_true, selectedFiberTerm]

/-- The selected output label is already in the finite image via the branch `(tail, 0)`. -/
def selectedIdealGroupLabel (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (tail : Fin problem.order) : (idealGroupRegister problem seed).Index :=
  idealGroupLabel problem seed (sourceFourierIndex problem tail, 0)

/-- The finite-image label stores the original seed times the advertised group power. -/
theorem selectedIdealGroupLabel_value (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (tail : Fin problem.order) :
    (selectedIdealGroupLabel problem seed tail).val =
      seed.toGroupPoint * problem.generator ^ tail.val := by
  simp [selectedIdealGroupLabel, idealGroupLabel, idealGroupOutput, sourceFourierIndex,
    SourceScope.oracleMultiplier]

/-- Distinct original residues give distinct finite-image group labels. -/
theorem selectedIdealGroupLabel_injective (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) : Function.Injective (selectedIdealGroupLabel problem seed) := by
  intro left right same
  have values := congrArg (fun label => label.val) same
  rw [selectedIdealGroupLabel_value, selectedIdealGroupLabel_value] at values
  have powers := (pow_inj_mod).mp (mul_left_cancel values)
  apply Fin.ext
  simpa [problem.order_eq_orderOf.symm, Nat.mod_eq_of_lt left.isLt,
    Nat.mod_eq_of_lt right.isLt] using powers

/-- Seed cancellation recovers exactly the original hidden-line source fiber. -/
theorem idealGroupLabel_selected_iff (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem) (left right tail : Fin problem.order) :
    idealGroupLabel problem seed
        (sourceFourierIndex problem left, sourceFourierIndex problem right) =
      selectedIdealGroupLabel problem seed tail ↔ left = fiberLeft problem input tail right := by
  constructor
  · intro same
    have values := congrArg (fun label => label.val) same
    have translated : seed.toGroupPoint *
        problem.toSourceScope.oracleMultiplier left.val right.val =
        seed.toGroupPoint * problem.generator ^ tail.val :=
      values.trans (selectedIdealGroupLabel_value problem seed tail)
    exact (oracleMultiplier_eq_generator_pow_iff problem input left right tail).mp
      (mul_left_cancel translated)
  · intro same
    apply Subtype.ext
    exact (congrArg (fun value => seed.toGroupPoint * value)
      ((oracleMultiplier_eq_generator_pow_iff problem input left right tail).mpr same)).trans
        (selectedIdealGroupLabel_value problem seed tail).symm

/-- The complete coherent Fourier sum over the actual original exponent basis. -/
def idealFiberAmplitude (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (frequency : (idealBranchRegister problem).Index)
    (output : (idealGroupRegister problem seed).Index) : ℂ :=
  ∑ right : Fin (2 ^ orderWidth problem), ∑ left : Fin (2 ^ orderWidth problem),
    (exponentReadoutCircuit problem).binaryMatrix (prodEquiv frequency) (prodEquiv (left, right)) *
      (if idealGroupLabel problem seed (left, right) = output then
        preparedBranchAmplitude problem (left, right) else 0)

private theorem preparedBranchAmplitude_selectedLabel
    (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (input : SecretInput problem) (left right : Fin (2 ^ orderWidth problem))
    (tail : Fin problem.order) :
    (if idealGroupLabel problem seed (left, right) = selectedIdealGroupLabel problem seed tail
      then preparedBranchAmplitude problem (left, right) else 0) =
    if hr : right.val < problem.order then
      if left.val = (fiberLeft problem input tail ⟨right.val, hr⟩).val then
        invSqrtOrder problem.order * invSqrtOrder problem.order else 0
    else 0 := by
  by_cases hr : right.val < problem.order
  · by_cases hl : left.val < problem.order
    · have labels := idealGroupLabel_selected_iff problem seed input
        (⟨left.val, hl⟩ : Fin problem.order) (⟨right.val, hr⟩ : Fin problem.order) tail
      have leftLift : sourceFourierIndex problem ⟨left.val, hl⟩ = left := Fin.ext rfl
      have rightLift : sourceFourierIndex problem ⟨right.val, hr⟩ = right := Fin.ext rfl
      rw [leftLift, rightLift, Fin.ext_iff] at labels
      simp [hr, labels, preparedBranchAmplitude, Concrete.BornBridge.exponentState_apply, hl]
    · have different : left.val ≠ (fiberLeft problem input tail ⟨right.val, hr⟩).val := by
        intro same
        exact hl (same ▸ (fiberLeft problem input tail ⟨right.val, hr⟩).isLt)
      simp [hr, different, preparedBranchAmplitude, Concrete.BornBridge.exponentState_apply, hl]
  · simp [hr, preparedBranchAmplitude, Concrete.BornBridge.exponentState_apply]

/-- The full original Fourier amplitude at a selected group label is the exact source sum. -/
theorem idealFiberAmplitude_selected_eq_sum (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem)
    (frequency : (idealBranchRegister problem).Index) (tail : Fin problem.order) :
    idealFiberAmplitude problem seed frequency (selectedIdealGroupLabel problem seed tail) =
      ∑ right : Fin problem.order,
        selectedFiberTerm input frequency.1 frequency.2 tail right := by
  unfold idealFiberAmplitude
  calc
    _ = ∑ right : Fin (2 ^ orderWidth problem), ∑ left : Fin (2 ^ orderWidth problem),
        star (invSqrtN (orderWidth problem) *
            ω (orderWidth problem) ^ (left.val * frequency.1.val)) *
          star (invSqrtN (orderWidth problem) *
            ω (orderWidth problem) ^ (right.val * frequency.2.val)) *
          (if hr : right.val < problem.order then
            if left.val = (fiberLeft problem input tail ⟨right.val, hr⟩).val then
              invSqrtOrder problem.order * invSqrtOrder problem.order else 0
          else 0) := by
      apply Finset.sum_congr rfl
      intro right _
      apply Finset.sum_congr rfl
      intro left _
      exact congrArg₂ (fun a b : ℂ => a * b)
        (exponentReadout_pair_entry problem (frequency.1, frequency.2) (left, right))
        (preparedBranchAmplitude_selectedLabel problem seed input left right tail)
    _ = ∑ right : Fin (2 ^ orderWidth problem),
        if hr : right.val < problem.order then
          selectedFiberTerm input frequency.1 frequency.2 tail ⟨right.val, hr⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro right _
      by_cases hr : right.val < problem.order
      · simp only [hr, dite_true]
        simp_rw [mul_ite, mul_zero]
        let selected := sourceFourierIndex problem (fiberLeft problem input tail ⟨right.val, hr⟩)
        rw [Fintype.sum_eq_single selected]
        · simp [selected, sourceFourierIndex, selectedFiberTerm]
        · intro other different
          have differentValue :
              other.val ≠ (fiberLeft problem input tail ⟨right.val, hr⟩).val := by
            intro same
            exact different (Fin.ext same)
          simp [differentValue]
      · simp [hr]
    _ = _ := sum_fin_fourierModulus_if_sourceRange problem
      (selectedFiberTerm input frequency.1 frequency.2 tail)

/-- The unchanged original selected frequencies retain the original amplitude lower bound. -/
theorem idealFiberAmplitude_selected_lower (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem) (unit : (ZMod problem.order)ˣ)
    (tail : Fin problem.order) :
    1 / (2 * (fourierModulus problem : ℝ)) ≤
      ‖idealFiberAmplitude problem seed
        (selectedIndex problem unit, selectedIndex problem (-input.secret * unit))
        (selectedIdealGroupLabel problem seed tail)‖ := by
  have equality := idealFiberAmplitude_selected_eq_sum problem seed input
    (selectedIndex problem unit, selectedIndex problem (-input.secret * unit)) tail
  exact (one_div_two_fourierModulus_le_norm_sum_selectedFiberTerm problem input unit tail).trans_eq
    (congrArg (fun value : ℂ => ‖value‖) equality).symm

/-- The certified operator on the original oracle image gives the complete coherent sum. -/
theorem idealReadout_extension_entry (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (Reference : Register)
    (vector : HilbertVector ((idealBranchRegister problem).prod Reference))
    (frequency : (idealBranchRegister problem).Index)
    (output : (idealGroupRegister problem seed).Index) (reference : Reference.Index) :
    (idealReadoutOperator problem seed Reference).applyVec
        (Effect.extensionVector (idealOracleEmbedding problem seed Reference) vector)
          ((prodEquiv frequency, output), reference) =
      ∑ right : Fin (2 ^ orderWidth problem), ∑ left : Fin (2 ^ orderWidth problem),
        (exponentReadoutCircuit problem).binaryMatrix
          (prodEquiv frequency) (prodEquiv (left, right)) *
          (if idealGroupLabel problem seed (left, right) = output then
            vector ((left, right), reference) else 0) := by
  change HilbertOperator.applyVec _ (Effect.extensionVector _ vector) _ = _
  rw [Effect.extensionVector, HilbertOperator.applyVec_sum]
  simp only [HilbertOperator.applyVec_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, HilbertOperator.applyVec_ket, idealReadoutOperator,
    UnitaryOperator.prodTensor_apply, idealOracleEmbedding]
  change (∑ branch : ((Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) ×
      Reference.Index), vector branch *
        ((exponentReadoutCircuit problem).binaryMatrix (prodEquiv frequency) (prodEquiv branch.1) *
          (if output = idealGroupLabel problem seed branch.1 then 1 else 0) *
          (if reference = branch.2 then 1 else 0))) = _
  simp only [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  by_cases same : idealGroupLabel problem seed (left, right) = output
  · simp only [same, if_true]
    exact mul_comm _ _
  · simp [same, Ne.symm same]

/-- Original prepared amplitudes retain an arbitrary coherent reference without alteration. -/
theorem idealReadout_prepared_entry (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (Reference : Register) (reference : HilbertVector Reference)
    (frequency : (idealBranchRegister problem).Index)
    (output : (idealGroupRegister problem seed).Index) (label : Reference.Index) :
    (idealReadoutOperator problem seed Reference).applyVec
        (Effect.extensionVector (idealOracleEmbedding problem seed Reference)
          (WithLp.toLp 2 (fun input => preparedBranchAmplitude problem input.1 *
            reference input.2))) ((prodEquiv frequency, output), label) =
      idealFiberAmplitude problem seed frequency output * reference label := by
  rw [idealReadout_extension_entry, idealFiberAmplitude, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro right _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  change _ * (if _ then preparedBranchAmplitude problem (left, right) * reference label else 0) = _
  split <;> simp_all only [mul_zero, zero_mul, mul_assoc]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
