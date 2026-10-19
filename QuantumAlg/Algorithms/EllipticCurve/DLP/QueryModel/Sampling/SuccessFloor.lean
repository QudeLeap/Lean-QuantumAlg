/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Outcome
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.FourierLaw
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Outcome
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected

/-!
# Original selected-family mass of the actual declared ECDLP sampler

The actual retained output law includes every original subgroup fiber. The
existing source floor is summed over those injectively encoded physical states,
then over all selected invertible residues [PZ03, ecc.tex:1531-1666].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open FiniteCyclicDLP.Canonical.Probability

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem

private def selectedRuntimeBasis (I : ECDLPInstance E) (input : SecretInput (problem I))
    (unit : (ZMod (problem I).order)ˣ) (index : Fin I.subgroupOrder) :
    (post I).register.Index :=
  runtimeBasis I (rawBasis I
    (selectedIndex (problem I) (unit : ZMod (problem I).order))
    (selectedIndex (problem I) (-input.secret * (unit : ZMod (problem I).order)))
    (selectedPointLabel I index))

private lemma selectedRuntimeBasis_injective (I : ECDLPInstance E)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ) :
    Function.Injective (selectedRuntimeBasis I input unit) := by
  intro left right same
  have binary := congrArg (fun basis =>
    (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) (basisEquiv I basis)) same
  simp only [selectedRuntimeBasis, runtimeBasis, Equiv.apply_symm_apply] at binary
  change prodEquiv (_, selectedPointLabel I left) =
    prodEquiv (_, selectedPointLabel I right) at binary
  exact selectedPointLabel_injective I (congrArg Prod.snd (prodEquiv.injective binary))

private lemma selectedRuntimeBasis_outcome (I : ECDLPInstance E)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ)
    (index : Fin I.subgroupOrder) :
    basisOutcome I (selectedRuntimeBasis I input unit index) =
      selectedRawOutcome (problem I) input unit := by
  rw [selectedRuntimeBasis, ecdlpSampling_basisOutcome_runtimeBasis]
  rfl

/-- Each selected raw result has its original floor in the actual retained output distribution. -/
public lemma ecdlpSampling_selectedOutcome_floor (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (secretInput : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ)
    {Reference : Register}
    (input : Execution.OracleInput (executionModel I).classicalOracles (pre I) Reference) :
    selectedRawOutcomePointwiseLowerBound (problem I) ≤
      (((run I expansion).outputDistribution (sourceEnvironment I A) input).map (observedOutcome I))
        (selectedRawOutcome (problem I) secretInput unit) := by
  let weight : (post I).register.Index → ENNReal := fun basis =>
    ENNReal.ofReal (if basisOutcome I basis = selectedRawOutcome (problem I) secretInput unit then
      ‖runtimeSourceState I A basis‖ ^ 2 else 0)
  have tailFloor (index : Fin I.subgroupOrder) :
      selectedTailPointwiseLowerBound (problem I) ≤
        weight (selectedRuntimeBasis I secretInput unit index) := by
    unfold weight
    rw [selectedRuntimeBasis_outcome, if_pos rfl, selectedRuntimeBasis,
      ecdlpSampling_runtimeSourceState_runtimeBasis]
    have amplitude := sourceState_selectedPointLabel_amplitude_floor I A secretInput unit index
    apply ENNReal.ofReal_le_ofReal
    change 1 / (4 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ) ^ 2) ≤ _
    calc
      _ = (1 / (2 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ))) ^ 2 := by
        field_simp
        ring
      _ ≤ _ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 amplitude
  rw [ecdlpSampling_run_outputProbability]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by split <;> positivity)]
  change selectedRawOutcomePointwiseLowerBound (problem I) ≤ ∑ basis, weight basis
  calc
    _ = ∑ index : Fin I.subgroupOrder, selectedTailPointwiseLowerBound (problem I) := by
      simp only [selectedRawOutcomePointwiseLowerBound, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]
      rfl
    _ ≤ ∑ index : Fin I.subgroupOrder,
        weight (selectedRuntimeBasis I secretInput unit index) :=
      Finset.sum_le_sum (fun index _ => tailFloor index)
    _ = (Finset.univ.image (selectedRuntimeBasis I secretInput unit)).sum weight := by
      rw [Finset.sum_image (selectedRuntimeBasis_injective I secretInput unit).injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro basis _; exact Finset.mem_univ basis)
      (fun basis _ _ => by positivity)

/-- The actual output retains the original complete selected-family probability floor. -/
public lemma ecdlpSampling_selectedFamily_floor (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (secretInput : SecretInput (problem I)) {Reference : Register}
    (input : Execution.OracleInput (executionModel I).classicalOracles (pre I) Reference) :
    selectedRawOutcomeFamilyLowerBound (problem I) ≤
      (selectedRawOutcomeFamily (problem I) secretInput).sum
        (((run I expansion).outputDistribution (sourceEnvironment I A) input).map
          (observedOutcome I)) := by
  let _ : NeZero (problem I).order := ⟨(problem I).order_ne_zero⟩
  rw [selectedRawOutcomeFamily]
  have imageSum := Finset.sum_image
    (s := Finset.univ)
    (f := fun outcome : FiniteCyclicDLP.Canonical.BornBridge.Outcome (problem I) =>
      ((run I expansion).outputDistribution (sourceEnvironment I A) input).map (observedOutcome
        I) outcome)
    (selectedRawOutcome_injective (problem I) secretInput).injOn
  change selectedRawOutcomeFamilyLowerBound (problem I) ≤
    (Finset.univ.image (selectedRawOutcome (problem I) secretInput)).sum
      (fun outcome => ((run I expansion).outputDistribution (sourceEnvironment I A) input).map
        (observedOutcome I)
        outcome)
  rw [imageSum]
  change Fintype.card (ZMod (problem I).order)ˣ •
    selectedRawOutcomePointwiseLowerBound (problem I) ≤ _
  calc
    _ = ∑ _unit : (ZMod (problem I).order)ˣ,
        selectedRawOutcomePointwiseLowerBound (problem I) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun unit _ =>
      ecdlpSampling_selectedOutcome_floor I A expansion secretInput unit input)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
