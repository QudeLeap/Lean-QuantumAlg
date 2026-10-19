/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Distribution
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.FourierLaw
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Outcome
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Distribution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected

/-!
# Original selected-family floor on actual subnormalized reused rounds

The complete original point-tail fibers contribute their source amplitude
floor. Summing the distinct tails and invertible residues gives the original
one-attempt lower bound. The same actual circuit returns this bound multiplied
by its incoming mass, including zero-mass and correlated failure fibers.
No normalized replacement input or independent-sampling premise is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

open Execution FiniteCyclicDLP.Canonical.Probability

attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local implicit_reducible] problem

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original complete selected-family real floor, determined by the public order. -/
public def successFloor (I : ECDLPInstance E) : ℝ :=
  FiniteCyclicDLP.Canonical.attemptFloor (problem I)

private def selectedBasis (I : ECDLPInstance E) (input : SecretInput (problem I))
    (unit : (ZMod (problem I).order)ˣ) (index : Fin I.subgroupOrder) :
    (context I).register.Index :=
  Sampling.runtimeBasis I (rawBasis I
    (selectedIndex (problem I) (unit : ZMod (problem I).order))
    (selectedIndex (problem I) (-input.secret * (unit : ZMod (problem I).order)))
    (selectedPointLabel I index))

private lemma selectedBasis_injective (I : ECDLPInstance E)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ) :
    Function.Injective (selectedBasis I input unit) := by
  intro left right same
  have binary := congrArg (fun basis =>
    (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
      (Sampling.basisEquiv I basis)) same
  simp only [selectedBasis, Sampling.runtimeBasis, Equiv.apply_symm_apply] at binary
  change prodEquiv (_, selectedPointLabel I left) =
    prodEquiv (_, selectedPointLabel I right) at binary
  exact selectedPointLabel_injective I (congrArg Prod.snd (prodEquiv.injective binary))

private lemma selectedBasis_outcome (I : ECDLPInstance E)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ)
    (index : Fin I.subgroupOrder) :
    basisOutcome I (selectedBasis I input unit index) =
      selectedRawOutcome (problem I) input unit := by
  change Sampling.basisOutcome I (Sampling.runtimeBasis I (rawBasis I _ _ _)) = _
  rw [Sampling.ecdlpSampling_basisOutcome_runtimeBasis]
  rfl

private lemma selectedBasis_amplitude (I : ECDLPInstance E) (A : Access I)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ)
    (index : Fin I.subgroupOrder) :
    runtimeSourceState I A (selectedBasis I input unit index) =
      sourceState I A (rawBasis I
        (selectedIndex (problem I) (unit : ZMod (problem I).order))
        (selectedIndex (problem I) (-input.secret * (unit : ZMod (problem I).order)))
        (selectedPointLabel I index)) := by
  change Sampling.runtimeSourceState I A (Sampling.runtimeBasis I _) = _
  exact Sampling.ecdlpSampling_runtimeSourceState_runtimeBasis I A _

private lemma selectedOutcome_source_floor (I : ECDLPInstance E) (A : Access I)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ) :
    (I.subgroupOrder : ℝ) / (4 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ) ^ 2) ≤
      ∑ basis : (context I).register.Index,
        if basisOutcome I basis = selectedRawOutcome (problem I) input unit then
          ‖runtimeSourceState I A basis‖ ^ 2 else 0 := by
  let weight : (context I).register.Index → ℝ := fun basis =>
    if basisOutcome I basis = selectedRawOutcome (problem I) input unit then
      ‖runtimeSourceState I A basis‖ ^ 2 else 0
  have tailFloor (index : Fin I.subgroupOrder) :
      1 / (4 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ) ^ 2) ≤
        weight (selectedBasis I input unit index) := by
    unfold weight
    rw [selectedBasis_outcome, if_pos rfl, selectedBasis_amplitude]
    have amplitude := sourceState_selectedPointLabel_amplitude_floor I A input unit index
    calc
      _ = (1 / (2 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ))) ^ 2 := by
        field_simp
        ring
      _ ≤ _ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 amplitude
  change _ ≤ ∑ basis, weight basis
  calc
    _ = ∑ _index : Fin I.subgroupOrder,
        1 / (4 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ∑ index : Fin I.subgroupOrder, weight (selectedBasis I input unit index) :=
      Finset.sum_le_sum (fun index _ => tailFloor index)
    _ = (Finset.univ.image (selectedBasis I input unit)).sum weight := by
      rw [Finset.sum_image (selectedBasis_injective I input unit).injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro basis _; exact Finset.mem_univ basis)
      (fun basis _ _ => by split <;> positivity)

private lemma selectedFamily_source_floor (I : ECDLPInstance E) (A : Access I)
    (input : SecretInput (problem I)) :
    successFloor I ≤
      (selectedRawOutcomeFamily (problem I) input).sum (fun outcome =>
        ∑ basis : (context I).register.Index,
          if basisOutcome I basis = outcome then ‖runtimeSourceState I A basis‖ ^ 2 else 0) := by
  let _ : NeZero (problem I).order := ⟨(problem I).order_ne_zero⟩
  rw [selectedRawOutcomeFamily,
    Finset.sum_image (selectedRawOutcome_injective (problem I) input).injOn]
  have numerical : successFloor I =
      (Fintype.card (ZMod (problem I).order)ˣ : ℝ) *
        ((I.subgroupOrder : ℝ) / (4 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ) ^ 2)) := by
    rw [ZMod.card_units_eq_totient]
    unfold successFloor FiniteCyclicDLP.Canonical.attemptFloor
      FiniteCyclicDLP.Canonical.successNumerator
      FiniteCyclicDLP.Canonical.successDenominator
    push_cast
    change ((I.subgroupOrder : ℝ) * _) / _ = _
    ring
  rw [numerical]
  calc
    _ = ∑ _unit : (ZMod (problem I).order)ˣ,
        (I.subgroupOrder : ℝ) / (4 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ) ^ 2) :=
      by simp
    _ ≤ _ := Finset.sum_le_sum (fun unit _ => selectedOutcome_source_floor I A input unit)

/-- The actual reused round keeps the original selected-family floor at its incoming mass. -/
public lemma ecdlpReuse_selectedFamily_mass_floor {allowAllocation : Bool}
    (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (input : SecretInput (problem I)) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I).HiddenState × History)) :
    state.mass * successFloor I ≤
      (selectedRawOutcomeFamily (problem I) input).sum (fun outcome =>
        ((((code (allowAllocation := allowAllocation) I expansion).execute (sourceEnvironment I A)
          Reference
            state).mapClassical
          (fun record => observedOutcome I (record.1.read (sampleInput I)))).block
            outcome).mass) := by
  simp only [ecdlpReuse_code_outcome_mass (allowAllocation := allowAllocation), ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (selectedFamily_source_floor I A input) state.mass_nonneg

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
