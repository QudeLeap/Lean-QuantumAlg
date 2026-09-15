/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Grover.Probability
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Algorithms.Grover.Specification
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# Grover's actual output distribution and exact marked-event probability

The final retained bit string is read from the one executed Circuit. Its
proved output distribution is the original mathematical Born readout of the
exact Grover vector. Canonical full-register decoding then recovers the
same basis index, preserving the source's exact sin-squared marked mass.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- The actual complete run has the original mathematical query-readout distribution. -/
theorem outputDistribution_eq {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    {Reference : Register} (input : Input pre Reference) :
    (run marked k).outputDistribution input =
      ((zMeasure (layout n)).outcomePMF (evolvedState marked k)).map CShape.Value.bits := by
  apply PMF.ext
  intro output
  have actual := congrArg (fun distribution : PMF (CShape.Value (.bits n)) =>
      distribution output)
    (ExecutionState.toPMF_mapClassical ((run marked k).execute Reference input.state)
      ((run marked k).execute_normalized input) (run marked k).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code marked k).execute Reference (input.state.mapClassical (fun store => (store, store)))
      |>.mapClassical (fun value => value.1.read (.storage (resultRef n k).toCStorageRef))
      |>.block output).mass) = _
  rw [code_block_mass marked k _ (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [TerminalZMeasure.outcomePMF, PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Function.comp_apply]
  by_cases matching : CShape.Value.bits ((zMeasure (layout n)).readout basis) = output
  · rw [if_pos matching, if_pos matching.symm]
    exact (QubitLayout.basisPMF_apply (evolvedState marked k) basis).symm
  · rw [if_neg matching, if_neg (Ne.symm matching)]
    exact ENNReal.ofReal_zero

/-- The actual relational marked event has the original exact success probability. -/
theorem actual_success {n t : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (counted : markedCount marked = t) (positive : 0 < t)
    {Reference : Register} (input : Input pre Reference) :
    ((run marked k).relationalDistribution input).toOuterMeasure
      {pair | accepts marked pair.1 pair.2} = exactSuccessProbability n t k := by
  have projection :
      ((run marked k).relationalDistribution input).toOuterMeasure
        {pair | accepts marked pair.1 pair.2} =
      ((run marked k).outputDistribution input).toOuterMeasure
        {result | match result with
          | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, outputDistribution_eq marked k input, PMF.toOuterMeasure_map_apply,
    TerminalZMeasure.outcomePMF, PMF.toOuterMeasure_map_apply]
  simp only [Set.preimage_ofPred_eq, TerminalZMeasure.fullRegisterIndex_zMeasure_readout]
  exact sourceSuccessProbability_eq marked counted positive

end

end QuantumAlg.GroverSearch
