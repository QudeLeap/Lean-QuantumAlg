/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect.Failure

/-!
# Original success floor for one actual complete ECDLP round

The real unaccepted fiber contracts by the original selected source floor.
Existing accepted input records are already sound and retain their first
success. Actual checked output support identifies the original bounded
scalar relation with the real accepted bit. The relational success proof
keeps all input, service and reference correlations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local irreducible] underPersistent

private theorem failure_le_mass {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {width scalar : Nat} {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalar) Reference (model.HiddenState × History)) :
    persistentFailureWeight (model := model) (ctx := ctx) (width := width) (scalarWidth := scalar)
      state ≤ state.mass := by
  simp only [persistentFailureWeight, ExecutionState.effectWeight,
    ExecutionState.mass, indicator_weight]
  apply Finset.sum_le_sum
  intro record _
  split_ifs
  · exact le_rfl
  · exact (state.block record).mass_nonneg

private theorem failure_nonneg {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {width scalar : Nat} {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalar) Reference (model.HiddenState × History)) :
    0 ≤ persistentFailureWeight (model := model) (ctx := ctx) (width := width)
      (scalarWidth := scalar) state := by
  simp only [persistentFailureWeight, ExecutionState.effectWeight, indicator_weight]
  apply Finset.sum_nonneg
  intro record _
  split_ifs
  · exact (state.block record).mass_nonneg
  · exact le_rfl

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

private theorem round_failure_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (context I) Reference ((Sampling.executionModel I A).HiddenState × History))
    (admitted : ∀ record, 0 < (state.block record).mass → roundStoreDomain I record.1) :
    persistentFailureWeight (model := Sampling.executionModel I A)
      (ctx := Sampling.Reuse.context I) (width := fieldWidth E) (scalarWidth := scalarWidth I)
      ((round I A expansion nontrivial).execute Reference state) ≤
        (1 - Sampling.Reuse.successFloor I) * state.mass := by
  let secretInput :=
    FiniteCyclicDLP.Canonical.Probability.SecretInput.ofKnownOrderProblem (problem I)
  have points := ecdlpRecovery_round_prefix_represents I A state
    (fun record present => (admitted record present).1)
  have contraction := sampledAttempt_failure_weight_le (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    I.basePoint.toMathlib I.targetPoint.toMathlib state
    (points (underPersistent (Sampling.Reuse.code I A expansion)
      (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (fieldWidth E) (scalarWidth I)))
    (Sampling.Reuse.successFloor I)
    ((ecdlpRecovery_sample_weight_bound I A expansion nontrivial secretInput _).trans_eq
      (indicator_decision_weight _ _ _ _))
  exact contraction.trans (mul_le_mul_of_nonneg_left
    (failure_le_mass (model := Sampling.executionModel I A) state)
    (sub_nonneg.mpr (successFloor_le_one I)))

private theorem entered_domain {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {History : Type} [Fintype History] {Reference : Register}
    (input : OracleInput model.classicalOracles ctx Reference) (history : Store ctx → History)
    (domain : Store ctx → Prop)
    (admitted : ∀ record, 0 < (input.localState.block record).mass → domain record.1) :
    ∀ record, 0 < ((input.state.mapClassical
      (fun entry => (entry.1, (entry.2, history entry.1)))).block record).mass →
        domain record.1 := by
  intro record positive
  obtain ⟨previous, same, present⟩ := (ExecutionState.mapClassical_block_mass_pos_iff input.state
    (fun entry => (entry.1, (entry.2, history entry.1))) record).mp positive
  have localPositive : 0 < (input.localState.block previous).mass := by
    simpa only [OracleInput.oracleInput_localState_block,
      DensityOperator.marginalLeft_mass] using present
  exact (congrArg Prod.fst same) ▸ admitted previous localPositive

omit [Fact p.Prime] in
/-- The same complete round meets the original selected-family relational success floor. -/
public theorem ecdlpRecovery_round_success (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles (context I) Reference)
    (admitted : roundInputDomain I A original.localState) :
    ENNReal.ofReal (Sampling.Reuse.successFloor I) ≤
      ((roundAlgorithm I A expansion nontrivial).relationalDistribution original).toOuterMeasure
        {pair | roundAccepts I pair.2} := by
  let : Fact p.Prime := ⟨E.prime⟩
  let actual := (roundAlgorithm I A expansion nontrivial).run
  let initial := original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have initialDomain := entered_domain (model := Sampling.executionModel I A)
    original id (roundStoreDomain I) admitted
  have failure := round_failure_le I A expansion nontrivial initial initialDomain
  rw [ExecutionState.mapClassical_mass, original.normalized, mul_one] at failure
  have agrees : ∀ record ∈ (actual.executionDistribution original).support,
      roundAccepts I (actual.result record) ↔ (roundSelectedPair I record.1).1 = true := by
    intro record supported
    have positive := (ExecutionState.mem_support_toPMF_iff (actual.execute Reference original.state)
      (actual.execute_normalized original) record).mp supported
    have sound := ecdlpRecovery_round_preserves_domain I A expansion nontrivial
      initial initialDomain record positive
    change ((roundSelectedPair I record.1).1 = true ∧
      (roundSelectedPair I record.1).2.toNat < I.subgroupOrder ∧
      (roundSelectedPair I record.1).2.toNat • I.basePoint.toMathlib = I.targetPoint.toMathlib) ↔ _
    exact ⟨fun accepted => accepted.1,
      fun flag => ⟨flag, sound.2.1, sound.2.2 flag⟩⟩
  have success := actual.relational_success_eq_one_sub_failure_effectWeight original
    (fun pair => roundAccepts I pair.2) (fun record => (roundSelectedPair I record.1).1) agrees
  change ENNReal.ofReal (Sampling.Reuse.successFloor I) ≤
    (actual.relationalDistribution original).toOuterMeasure {pair | roundAccepts I pair.2}
  rw [success]
  have nonnegative := failure_nonneg (model := Sampling.executionModel I A)
    ((round I A expansion nontrivial).execute Reference initial)
  have reads : (actual.execute Reference original.state).effectWeight
      (fun record => if (roundSelectedPair I record.1).1 = false then
        Effect.one ((context I).register.prod Reference)
      else Effect.zero ((context I).register.prod Reference)) =
      persistentFailureWeight (model := Sampling.executionModel I A)
        ((round I A expansion nontrivial).execute Reference initial) := by
    exact indicator_decision_weight _ _ _ _
  rw [reads, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ nonnegative]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
