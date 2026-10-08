/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Probability
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual amplitude-estimation probabilities and the original success bound

The unique execution's packed phase result has the source's coherent Born
readout. Both signed eigenphase windows yield the same additive-error event,
so the actual relational distribution has confidence at least one minus eta.

-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- The actual complete run has the original mathematical query-readout distribution. -/
theorem outputDistribution_eq {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (empty : Elementary.helperWidth t n = 0)
    {Reference : Register} (input : OracleInput (model E).classicalOracles pre Reference) :
    (run E t).outputDistribution input =
      (outcomeDistribution E t).map CShape.Value.bits := by
  apply PMF.ext
  intro output
  have actual := congrArg (fun distribution : PMF (CShape.Value (.bits t)) =>
      distribution output)
    (ExecutionState.toPMF_mapClassical ((run E t).execute Reference input.state)
      ((run E t).execute_normalized input) (run E t).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code E t).execute Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      |>.mapClassical (fun value => value.1.read (.storage (resultRef t n).toCStorageRef))
      |>.block output).mass) = _
  rw [code_block_mass E t empty _ (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [outcomeDistribution, TerminalZMeasure.outcomePMF, PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Function.comp_apply]
  by_cases matching : CShape.Value.bits ((qpeMeasurement t n).readout basis) = output
  · rw [if_pos matching, if_pos matching.symm]
    exact (QubitLayout.basisPMF_apply (evolvedState E t) basis).symm
  · rw [if_neg matching, if_neg (Ne.symm matching)]
    exact ENNReal.ofReal_zero

private theorem accepts_iff_encoded {n t : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps : Real) (initial : Store pre) (result : CShape.Value (.bits t)) :
    accepts E eps initial result ↔
      result ∈ CShape.Value.bits '' {outcome | SuccessfulOutcome E eps outcome} := by
  cases result with
  | bits actual =>
      constructor
      · intro accepted
        exact ⟨actual, accepted, rfl⟩
      · rintro ⟨outcome, accepted, same⟩
        have sameBits : outcome = actual := CShape.Value.bits.inj same
        subst outcome
        exact accepted

/-- The independent additive-error event holds on the actual initial-store/result distribution. -/
theorem actual_success {n : Nat} (E : GeneralAmplitudeEstimationInput n) (eps η : Real)
    (positiveWidth : 0 < selectedPhaseQubits eps η)
    (positivePrecision : 0 < eps) (precisionAtMostOne : eps ≤ 1)
    (positiveFailure : 0 < η) (failureAtMostOne : η ≤ 1)
    {Reference : Register} (input : OracleInput (model E).classicalOracles pre Reference) :
    ENNReal.ofReal (1 - η) ≤
      ((run E (selectedPhaseQubits eps η)).relationalDistribution input).toOuterMeasure
        {pair | accepts E eps pair.1 pair.2} := by
  have projection :
      ((run E (selectedPhaseQubits eps η)).relationalDistribution input).toOuterMeasure
        {pair | accepts E eps pair.1 pair.2} =
      ((run E (selectedPhaseQubits eps η)).outputDistribution input).toOuterMeasure
        (CShape.Value.bits '' {outcome | SuccessfulOutcome E eps outcome}) := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext record
    exact accepts_iff_encoded E eps record.2.2.1
      ((run E (selectedPhaseQubits eps η)).result record)
  have empty := Elementary.selected_helperWidth_eq_zero n positivePrecision precisionAtMostOne
    positiveFailure failureAtMostOne
  rw [projection, outputDistribution_eq E (selectedPhaseQubits eps η) empty input,
    PMF.toOuterMeasure_map_apply,
    Set.preimage_image_eq _ (fun _ _ same => CShape.Value.bits.inj same)]
  exact outcomeSuccessProbability_ge_one_sub_eta E eps η positiveWidth
    positivePrecision positiveFailure failureAtMostOne

end

end QuantumAlg.AmplitudeEstimation
