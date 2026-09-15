/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Probability
import all QuantumAlg.Algorithms.OrderFinding.BornModel
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# The native sample has the original order-finding distribution

Actual preparation, the original source-query sequence, Z writes and bit
packing yield the source phase-register marginal for every external reference.
The proof is independent of subsequent exact-grid or continued-fraction recovery.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution
open QuantumAlg.OrderFinding.BornBridge

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- The actual complete run has the original mathematical query-readout distribution. -/
theorem outputDistribution_eq {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} (input : Execution.Input ctx Reference) :
    (run ctx noQuantum A).outputDistribution input =
      ((measurement t n).outcomePMF (evolvedState A)).map CShape.Value.bits := by
  apply PMF.ext
  intro output
  have actual := congrArg (fun distribution : PMF (CShape.Value (.bits t)) =>
      distribution output)
    (ExecutionState.toPMF_mapClassical ((run ctx noQuantum A).execute Reference input.state)
      ((run ctx noQuantum A).execute_normalized input) (run ctx noQuantum A).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code ctx noQuantum A).execute Reference
      (input.state.mapClassical (fun store => (store, store)))
      |>.mapClassical (fun value => value.1.read
        (.storage (resultRef ctx noQuantum t n).toCStorageRef))
      |>.block output).mass) = _
  rw [code_block_mass ctx noQuantum A _ (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [TerminalZMeasure.outcomePMF, PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Function.comp_apply]
  by_cases matching : CShape.Value.bits ((measurement t n).readout basis) = output
  · rw [if_pos matching, if_pos matching.symm]
    exact (QubitLayout.basisPMF_apply (evolvedState A) basis).symm
  · rw [if_neg matching, if_neg (Ne.symm matching)]
    exact ENNReal.ofReal_zero

end

end QuantumAlg.OrderFinding.Sampling.Framed
