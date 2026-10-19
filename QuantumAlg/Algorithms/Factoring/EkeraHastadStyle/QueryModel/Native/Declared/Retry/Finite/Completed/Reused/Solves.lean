/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Success
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.State
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Space

/-!
# Full input-based contract of a physically reused EH batch

One actual next batch consumes the live sound selector and original bank,
executes recovery and first-success selection, pays its output pack and reset,
and satisfies the independently stated success, state, borrowed and resource
obligations for arbitrary correlated caller, service and reference inputs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private lemma nextCompleted_relationalSuccess
    {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference)
    (admitted : selectedSound base noQuantum N original.localState) :
    1 - AllKeys.sourceFailure input ≤
      ((nextCompletedAlgorithm base noQuantum N input).relationalDistribution (sourceEnvironment
        input) original).toOuterMeasure
        {pair | (nextCompletedProblem base noQuantum N input).accepts (sourceEnvironment input)
          () pair.1 pair.2} := by
  have projection :
      ((nextCompletedAlgorithm base noQuantum N input).relationalDistribution (sourceEnvironment
        input) original).toOuterMeasure
          {pair | (nextCompletedProblem base noQuantum N input).accepts (sourceEnvironment
            input) () pair.1 pair.2} =
        ((nextCompletedRun base noQuantum N input).outputDistribution (sourceEnvironment input)
          original).toOuterMeasure (AllKeys.accepts N) := by
    simp only [Algorithm.relationalDistribution, nextCompletedAlgorithm,
      nextCompletedProblem, AlgorithmRun.relationalDistribution,
      AlgorithmRun.outputDistribution, PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact nextCompletedRun_successProbability base noQuantum N input original admitted

/-- The actual reused EH batch solves its input-based independent one-batch
problem, including success, pure bank reset, borrowed restoration and every
supported path's event, fixed-space and serial-depth allowances. -/
lemma nextCompletedAlgorithm_solves :
    Algorithm.Solves (nextCompletedAlgorithm base noQuantum N input)
      (nextCompletedProblem base noQuantum N input) := by
  constructor
  · intro environment _witness Reference original valid admitted
    have same : environment = sourceEnvironment input := valid
    subst environment
    exact nextCompleted_relationalSuccess base noQuantum N input original admitted
  · intro environment _witness Reference original _valid _admitted requirement present
    have same : requirement = nextStateRequirement base noQuantum N :=
      List.mem_singleton.mp present
    subst requirement
    exact nextCompleted_stateRequirement_holds base noQuantum N input original
  · intro environment _witness Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (nextCompleted_restartCleanup base noQuantum input).restores reference state
  · intro _environment _witness _Reference _original _valid _admitted path _supported
    exact nextCompleted_resourcePool_le base noQuantum N input path
  · intro _environment _witness _Reference _original _valid _admitted path _supported
    exact nextCompleted_peakResidentSpace_le base noQuantum N input path
  · intro _environment _witness _Reference _original _valid _admitted path _supported
    exact nextCompleted_peakAuxiliarySpace_le base noQuantum N input path
  · intro _environment _witness _Reference _original _valid _admitted path _supported
    exact nextCompleted_depth_le base noQuantum N input Resource.Event.quantumDuration path

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
