/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Correctness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Candidate
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Prefix
import all QuantumAlg.Util.PMF

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model

/-!
# Actual full-run bounded-scalar success and original public calibration
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

attribute [local instance] Classical.decEq Classical.propDecidable

private theorem optional_nonempty_probability {shape : CShape}
    (distribution : PMF (CShape.option shape).Value) :
    distribution.toOuterMeasure {value | value ≠ .optionNone} =
      1 - distribution .optionNone := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {value : (CShape.option shape).Value | ¬ value ≠ .optionNone} =
      ({.optionNone} : Set (CShape.option shape).Value) := by
    ext value
    simp
  rw [complement, PMF.toOuterMeasure_apply_singleton]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual full packed run has the original finite geometric success floor. -/
public theorem ecdlpRecovery_run_success (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    1 - ENNReal.ofReal ((1 - Sampling.Reuse.successFloor I) ^ count) ≤
      ((run I A expansion nontrivial count).relationalDistribution original).toOuterMeasure
        {pair | wholeAccepts I pair.2} := by
  let : Fact p.Prime := ⟨E.prime⟩
  let witness := FiniteCyclicDLP.Canonical.Probability.SecretInput.ofKnownOrderProblem (problem I)
  let actual := run I A expansion nontrivial count
  let distribution := actual.outputDistribution original
  have sound : ∀ output ∈ distribution.support,
      wholeAccepts I output ↔ output ≠ .optionNone := by
    intro output supported
    cases output with
    | optionNone =>
        change False ↔ (.optionNone : (CShape.option (.unsignedWord (scalarWidth I))).Value) ≠
          .optionNone
        exact ⟨False.elim, fun absent => absent rfl⟩
    | optionSome value =>
        have correct := ecdlpRecovery_run_output_correct I A expansion nontrivial count witness
          original valid value supported
        have bounded : value.toNat < I.subgroupOrder := by
          rw [correct]
          exact (FiniteCyclicDLP.Canonical.Probability.residueIndex (problem I)
            witness.secret).isLt
        have equation := (bounded_scalar_target_iff I witness value.toNat bounded).mpr correct
        simp only [wholeAccepts]
        constructor
        · intro _ same
          cases same
        · intro _
          exact ⟨bounded, equation⟩
  have eventEq : distribution.toOuterMeasure {output | wholeAccepts I output} =
      distribution.toOuterMeasure {output | output ≠ .optionNone} := by
    apply distribution.toOuterMeasure_apply_eq_of_inter_support_eq
    ext output
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact and_congr_left (fun supported => sound output supported)
  have projection := AlgorithmRun.relationalDistribution_map_output actual original
  have projected := congrArg (fun law : PMF (CShape.option (.unsignedWord (scalarWidth I))).Value =>
    law.toOuterMeasure {output | wholeAccepts I output}) projection
  rw [PMF.toOuterMeasure_map_apply] at projected
  calc
    1 - ENNReal.ofReal ((1 - Sampling.Reuse.successFloor I) ^ count) ≤
        1 - distribution .optionNone :=
      tsub_le_tsub_left
        (ecdlpRecovery_run_none_probability_le I A expansion nontrivial count witness
          original valid) 1
    _ = distribution.toOuterMeasure {output | output ≠ .optionNone} :=
      (optional_nonempty_probability distribution).symm
    _ = distribution.toOuterMeasure {output | wholeAccepts I output} := eventEq.symm
    _ = (actual.relationalDistribution original).toOuterMeasure
        {pair | wholeAccepts I pair.2} := projected.symm



/-- The same actual declared-query run reaches the original requested public failure budget. -/
public theorem ecdlpRecovery_run_calibrated_success (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    Factoring.FailureBudget.successThreshold budget ≤
      ((run I A expansion nontrivial (retryCountForBudget I budget)).relationalDistribution
        original).toOuterMeasure {pair | wholeAccepts I pair.2} := by
  have calibrated :=
    FiniteCyclicDLP.Concrete.Amplification.successThreshold_le_one_sub_retryFailurePower
      (problem I) budget wellFormed
  have nonnegative := Factoring.FailureBudget.value_nonneg
    (FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget (problem I))
    (FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget_strictlyWellFormed
      (problem I)).toWellFormed
  rw [← ENNReal.ofReal_pow nonnegative,
    FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget_value] at calibrated
  exact calibrated.trans (ecdlpRecovery_run_success I A expansion nontrivial
    (retryCountForBudget I budget) original valid)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
