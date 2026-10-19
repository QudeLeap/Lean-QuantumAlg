/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Pipeline

import all QuantumAlg.Primitives.WalshHadamard.Readout.Probability
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.WalshHadamard

/-!
# The output distribution of the actual Walsh-Hadamard execution

The distribution below is obtained from the actual final Store blocks.
The original mathematical Born distribution is used only on the right of a
proved equality, after actual preparation, measurement writes and packing
have already determined every block mass.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- The actual complete run has the original mathematical query-readout distribution. -/
lemma outputDistribution_eq {n : Nat} (f : WalshHadamard.Oracle n)
    {Reference : Register} (input : OracleInput ClassicalOracleModel.empty pre Reference) :
    ((run n).outputDistribution (environment f)) input =
      ((measurement n).outcomePMF
        (evolvedState f)).map
          CShape.Value.bits := by
  apply PMF.ext
  intro output
  have actual := congrArg (fun distribution : PMF (CShape.Value (.bits n)) =>
      distribution output)
    (ExecutionState.toPMF_mapClassical ((run n).execute (environment f) Reference input.state)
      (((run n).execute_normalized (environment f)) input) (run n).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code n).execute (environment f) Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      |>.mapClassical (fun value => value.1.read (.storage (resultRef n).toCStorageRef))
      |>.block output).mass) = _
  rw [code_block_mass f _ (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [TerminalZMeasure.outcomePMF, PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro basis _
  have evolved :
      (evolvedState f).normalized =
          WalshHadamard.finalJointState f :=
    evolvedState_normalized f
  simp only [Function.comp_apply]
  by_cases matching : CShape.Value.bits ((measurement n).readout basis) = output
  · rw [if_pos matching, if_pos matching.symm]
    exact (congrArg
      (fun vector : NormalizedVector (Qubits (n + 1)) =>
        ENNReal.ofReal (‖vector basis‖ ^ 2)) evolved.symm).trans
      (QubitLayout.basisPMF_apply _ basis).symm
  · rw [if_neg matching, if_neg (Ne.symm matching)]
    exact ENNReal.ofReal_zero

end

end QuantumAlg.WalshHadamard.Readout
