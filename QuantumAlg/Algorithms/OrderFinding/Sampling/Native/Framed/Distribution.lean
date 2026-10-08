/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Probability
import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Distribution
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# Distribution of the complete selected native source sample

Actual preparation, declared-query native gates, physical Z writes and word
packing yield the source phase-register marginal for every normalized input
with arbitrary classical and external-reference correlations.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- The actual sampler output law equals the native source Born law. -/
theorem outputDistribution_eq {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput (model access).classicalOracles ctx Reference) :
    (run ctx noQuantum access).outputDistribution input =
      (OrderFinding.Native.sourceOutcomePMF access).map CShape.Value.bits := by
  apply PMF.ext
  intro output
  have actual := congrArg (fun distribution : PMF (CShape.Value (.bits t)) =>
      distribution output)
    (ExecutionState.toPMF_mapClassical ((run ctx noQuantum access).execute Reference input.state)
      ((run ctx noQuantum access).execute_normalized input)
      (run ctx noQuantum access).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code ctx noQuantum access).execute Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      |>.mapClassical (fun value => value.1.read
        (.storage (resultRef ctx noQuantum t width).toCStorageRef))
      |>.block output).mass) = _
  rw [code_block_mass ctx noQuantum access _
    (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [OrderFinding.Native.sourceOutcomePMF, TerminalZMeasure.outcomePMF,
    PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Function.comp_apply]
  by_cases matching :
      CShape.Value.bits ((OrderFinding.Native.measurement t width).readout basis) = output
  · rw [if_pos matching, if_pos matching.symm]
    exact (QubitLayout.basisPMF_apply (OrderFinding.Native.evolvedState access) basis).symm
  · rw [if_neg matching, if_neg (Ne.symm matching)]
    exact ENNReal.ofReal_zero

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
