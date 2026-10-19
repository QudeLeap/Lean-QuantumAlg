/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Circuit.Marginal
import all QuantumAlg.Core.Execution.State.Marginal.Reference
import all QuantumAlg.Core.Execution.Input.Oracle.Reference

/-!
# Original complete runs under an external reference projection

The initial Store is retained by the same AlgorithmRun execution before and
after tracing the reference factor. No execution result is supplied as data.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

private lemma forgetReferenceFrame_map_decisions
    {C D : Type} [Fintype C] [Fintype D] {R Frame Reference : Register}
    {decision : DecidableEq D} (state : ExecutionState C (R.prod (Frame.prod Reference)))
    (read : C → D) :
    (@ExecutionState.mapClassical C D _ _ _ decision state read).forgetReferenceFrame =
      @ExecutionState.mapClassical C D _ _ _ decision state.forgetReferenceFrame read :=
  @ExecutionState.forgetReferenceFrame_mapClassical C D _ _ R Frame Reference decision state read

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
  (run : AlgorithmRun model pre post shape false) (environment : model.Environment)
  {Reference Frame : Register}

/-- Every complete real run commutes with tracing a separate external reference factor. -/
lemma execute_forgetReferenceFrame
    (input : State pre (Frame.prod Reference) model.HiddenState) :
    run.execute environment Reference input.forgetReferenceFrame =
      (run.execute environment (Frame.prod Reference) input).forgetReferenceFrame := by
  unfold execute
  rw [← forgetReferenceFrame_map_decisions]
  exact run.code.execute_forgetReferenceFrame environment _

/-- Reference projection leaves the probability of every actual full execution record intact. -/
lemma executionDistribution_forgetReferenceFrame
    (input : OracleInput model.classicalOracles pre (Frame.prod Reference)) :
    run.executionDistribution environment input.forgetReferenceFrame =
      run.executionDistribution environment input := by
  apply PMF.ext
  intro record
  unfold executionDistribution
  rw [ExecutionState.toPMF_apply, ExecutionState.toPMF_apply]
  change ENNReal.ofReal
      (((run.execute environment Reference input.state.forgetReferenceFrame).block record).mass) = _
  rw [run.execute_forgetReferenceFrame, ExecutionState.forgetReferenceFrame_block_mass]

/-- The actual initial store and final result have the same joint law after reference tracing. -/
lemma relationalDistribution_forgetReferenceFrame
    (input : OracleInput model.classicalOracles pre (Frame.prod Reference)) :
    run.relationalDistribution environment input.forgetReferenceFrame =
      run.relationalDistribution environment input := by
  unfold relationalDistribution
  rw [run.executionDistribution_forgetReferenceFrame]

end

end QuantumAlg.AlgorithmRun
