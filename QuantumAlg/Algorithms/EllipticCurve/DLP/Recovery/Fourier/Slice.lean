/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Fiber
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency

/-!
# Exact coherent slices of the existing original Fourier operator

The entry theorem is a finite-index repackaging of the existing
idealReadout_extension_entry. The family theorem retains all collisions
of group labels and all Reference amplitudes before taking any norm.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open FiniteCyclicDLP ConcreteCircuitAccess
open QuantumFourierTransform QuantumFourierTransform.Semiclassical
open scoped BigOperators

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private lemma group_reference_sum_apply {Branch : Type} [Fintype Branch]
    {Group Reference : Register} (group : Branch → Group.Index)
    (coefficient : Branch → Reference.Index → ℂ)
    (output : Group.Index) (ref : Reference.Index) :
    (∑ branch, ∑ index : Reference.Index,
      coefficient branch index •
        (NormalizedVector.ket (R := Group.prod Reference) (group branch, index)).vec)
        (output, ref) =
      ∑ branch, if group branch = output then coefficient branch ref else 0 := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, NormalizedVector.ket_apply, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro branch _
  by_cases same : group branch = output
  · rw [if_pos same]
    calc
      _ = if (output, ref) = (group branch, ref) then coefficient branch ref else 0 := by
        apply Finset.sum_eq_single ref
        · intro index _ different
          have noPair : ((output, ref) : (Group.prod Reference).Index) ≠
              (group branch, index) := by
            intro equal
            exact different (congrArg (fun label => label.2) equal).symm
          exact if_neg noPair
        · intro missing
          exact (missing (Finset.mem_univ ref)).elim
      _ = _ := by simp only [same, if_true]
  · rw [if_neg same]
    apply Finset.sum_eq_zero
    intro index _
    have noPair : ((output, ref) : (Group.prod Reference).Index) ≠
        (group branch, index) := by
      intro equal
      exact same (congrArg (fun label => label.1) equal).symm
    exact if_neg noPair

private lemma finite_fiber_sum {Input Branch : Type} [Fintype Input] [Fintype Branch]
    [DecidableEq Input]
    (input : Branch → Input) (coefficient : Input → ℂ)
    (selected : Input → Prop) [DecidablePred selected] (amplitude : Branch → ℂ) :
    (∑ label : Input,
      if selected label then coefficient label *
        (∑ branch, if input branch = label then amplitude branch else 0) else 0) =
      ∑ branch, if selected (input branch) then
        coefficient (input branch) * amplitude branch else 0 := by
  calc
    _ = ∑ label : Input, ∑ branch,
        if input branch = label then
          (if selected label then coefficient label * amplitude branch else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro label _
      by_cases accepted : selected label
      · simp only [if_pos accepted, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro branch _
        by_cases same : input branch = label <;> simp [same]
      · simp [accepted]
    _ = ∑ branch, ∑ label : Input,
        if input branch = label then
          (if selected label then coefficient label * amplitude branch else 0) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro branch _
      simp

/-- The certified paired readout has precisely the two existing complete native rows. -/
lemma exponentReadout_fullRows (problem : KnownOrderProblem E.GroupPoint)
    (frequency branch : (idealBranchRegister problem).Index) :
    ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
        (prodEquiv frequency) (prodEquiv branch) =
      Partner.fullRows true (orderWidth problem) frequency.1
          ((binaryEquiv (orderWidth problem)).symm branch.1) *
        Partner.fullRows true (orderWidth problem) frequency.2
          ((binaryEquiv (orderWidth problem)).symm branch.2) := by
  change Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem) at frequency branch
  rw [exponentReadoutCircuit_binaryMatrix, UnitaryOperator.tensor_apply]
  simp only [Equiv.symm_apply_apply, Partner.fullRows, if_true,
    Native.qftNative_inverseCircuit_binaryMatrix, Equiv.apply_symm_apply]

/-- Each raw-vector slice is the original full coherent sum, including every group collision. -/
lemma idealReadoutSlice_extension_entry (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (Reference : Register)
    (vector : HilbertVector ((idealBranchRegister problem).prod Reference))
    (frequency : (idealBranchRegister problem).Index)
    (output : (idealGroupRegister problem seed).Index) (ref : Reference.Index) :
    idealReadoutSlice problem seed Reference
        ((idealReadoutOperator problem seed Reference).applyVec
          (Effect.extensionVector (idealOracleEmbedding problem seed Reference) vector))
        frequency (output, ref) =
      ∑ branch : (idealBranchRegister problem).Index,
        if idealGroupLabel problem seed branch = output then
          ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
            (prodEquiv frequency) (prodEquiv branch) * vector (branch, ref) else 0 := by
  change (idealReadoutOperator problem seed Reference).applyVec
    (Effect.extensionVector (idealOracleEmbedding problem seed Reference) vector)
      ((prodEquiv frequency, output), ref) = _
  rw [idealReadout_extension_entry]
  simp only [mul_ite, mul_zero]
  exact (Fintype.sum_prod_type_right
    (fun branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem) =>
      if idealGroupLabel problem seed branch = output then
        ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
          (prodEquiv frequency) (prodEquiv branch) * vector (branch, ref) else 0)).symm

/-- An arbitrary finite coherent source family keeps the exact original Fourier slice. -/
lemma idealReadoutSlice_extension_family (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (Reference : Register)
    {Branch : Type} [Fintype Branch]
    (input : Branch → (idealBranchRegister problem).Index) (amplitude : Branch → ℂ)
    (reference : HilbertVector Reference)
    (frequency : (idealBranchRegister problem).Index) :
    idealReadoutSlice problem seed Reference
        ((idealReadoutOperator problem seed Reference).applyVec
          (Effect.extensionVector (idealOracleEmbedding problem seed Reference)
            (∑ branch, ∑ ref : Reference.Index,
              (amplitude branch * reference ref) •
                (NormalizedVector.ket (R := (idealBranchRegister problem).prod Reference)
                  (input branch, ref)).vec))) frequency =
      ∑ branch, ∑ ref : Reference.Index,
        ((amplitude branch *
          ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
            (prodEquiv frequency) (prodEquiv (input branch))) * reference ref) •
          (NormalizedVector.ket
            (R := (idealGroupRegister problem seed).prod Reference)
            (idealGroupLabel problem seed (input branch), ref)).vec := by
  apply WithLp.ofLp_injective
  funext label
  rcases label with ⟨output, ref⟩
  rw [idealReadoutSlice_extension_entry, group_reference_sum_apply]
  simp_rw [group_reference_sum_apply]
  refine (@finite_fiber_sum (idealBranchRegister problem).Index Branch
    (idealBranchRegister problem).fintype inferInstance (idealBranchRegister problem).decEq input
    (fun label =>
      ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
        (prodEquiv frequency) (prodEquiv label))
    (fun label => idealGroupLabel problem seed label = output)
    (fun label => (idealGroupRegister problem seed).decEq
      (idealGroupLabel problem seed label) output)
    (fun branch => amplitude branch * reference ref)).trans ?_
  apply Finset.sum_congr rfl
  intro branch _
  by_cases selected : idealGroupLabel problem seed (input branch) = output
  · simp only [if_pos selected]
    ac_rfl
  · simp only [if_neg selected]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
