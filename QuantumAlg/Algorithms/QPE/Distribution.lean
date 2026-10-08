/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Probability
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual phase-estimation probabilities and the original success bound

The unique execution's packed phase result has the source's coherent Born
readout. The original circular phase window therefore has probability at least
four over pi squared in the same actual initial-store/result distribution.

-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- The actual complete run has the original mathematical query-readout distribution. -/
theorem outputDistribution_eq {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} (input : OracleInput ClassicalOracleModel.empty (pre t n) Reference)
    (promised : inputPromise P t input.caller.localState.quantumMarginal) :
    (run P t).outputDistribution input =
      ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).map CShape.Value.bits := by
  apply PMF.ext
  intro output
  have actual := congrArg (fun distribution : PMF (CShape.Value (.bits t)) =>
      distribution output)
    (ExecutionState.toPMF_mapClassical ((run P t).execute Reference input.state)
      ((run P t).execute_normalized input) (run P t).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code P t).execute Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      |>.mapClassical (fun value => value.1.read (.storage (resultRef t n).toCStorageRef))
      |>.block output).mass) = _
  have actualPromise : inputPromise P t
      (input.state.mapClassical
        (fun value => (value.1, (value.2, value.1)))).quantumMarginal.marginalLeft := by
    rw [Input.localState_quantumMarginal, OracleInput.oracleInput_caller_quantumMarginal]
      at promised
    simpa only [ExecutionState.mapClassical_quantumMarginal] using promised
  rw [code_block_mass P t _ actualPromise]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [TerminalZMeasure.outcomePMF, PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Function.comp_apply]
  by_cases matching : CShape.Value.bits ((qpeMeasurement t n).readout basis) = output
  · rw [if_pos matching, if_pos matching.symm]
    exact (QubitLayout.basisPMF_apply (qpeEvolvedState P t) basis).symm
  · rw [if_neg matching, if_neg (Ne.symm matching)]
    exact ENNReal.ofReal_zero

private theorem accepts_iff_encoded {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (initial : Store (pre t n)) (result : CShape.Value (.bits t)) :
    accepts P t initial result ↔
      result ∈ CShape.Value.bits '' {outcome | SuccessfulOutcome P t outcome} := by
  cases result with
  | bits actual =>
      constructor
      · intro accepted
        exact ⟨actual, accepted, rfl⟩
      · rintro ⟨outcome, accepted, same⟩
        have sameBits : outcome = actual := CShape.Value.bits.inj same
        subst outcome
        exact accepted

/-- The original circular precision event holds on the actual initial-store/result distribution. -/
theorem actual_success {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} (input : OracleInput ClassicalOracleModel.empty (pre t n) Reference)
    (promised : inputPromise P t input.caller.localState.quantumMarginal) :
    ENNReal.ofReal (4 / Real.pi ^ 2) ≤
      ((run P t).relationalDistribution input).toOuterMeasure
        {pair | accepts P t pair.1 pair.2} := by
  have projection :
      ((run P t).relationalDistribution input).toOuterMeasure
        {pair | accepts P t pair.1 pair.2} =
      ((run P t).outputDistribution input).toOuterMeasure
        (CShape.Value.bits '' {outcome | SuccessfulOutcome P t outcome}) := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext record
    exact accepts_iff_encoded P t record.2.2.1 ((run P t).result record)
  rw [projection, outputDistribution_eq P t input promised, PMF.toOuterMeasure_map_apply,
    Set.preimage_image_eq _ (fun _ _ same => CShape.Value.bits.inj same)]
  exact born_successProbability_ge P t

end

end QuantumAlg.QuantumPhaseEstimation
