/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.NextProblem
import all QuantumAlg.Core.Execution.Reference.Probability.Kernel

/-!
# Conditional readout of one physically reused EH batch

The final-state observation hides internal paths before comparing the actual
factor cell with the independent source batch law.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma outputDistribution_eq_finalState_read
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape) (environment : model.Environment)
    {Reference : Register}
    (original : Execution.OracleInput model.classicalOracles pre Reference) :
    run.outputDistribution environment original =
      ((run.finalState environment Reference original.state).toPMF
        ((run.finalState_mass environment Reference original.state).trans
          original.normalized)).map
        run.output.eval := by
  change ((run.execute environment Reference original.state).toPMF
      (run.execute_normalized environment original)).map
      (fun record => run.output.eval record.1) = _
  unfold AlgorithmRun.finalState
  rw [ExecutionState.toPMF_mapClassical, PMF.map_comp]
  rfl


/-- An input-dependent final-store law follows from its full reference kernel. -/
private lemma finalState_distribution_of_reference
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape) (environment : model.Environment)
    {Reference : Register}
    (original : Execution.OracleInput model.classicalOracles pre Reference)
    {Outcome : Type} [Finite Outcome]
    (read : Execution.Store post → Outcome)
    (kernel : (Execution.Store pre ×
      (model.HiddenState × Execution.Store pre)) → PMF Outcome)
    (observed : ∀ value (left right : Reference.Index),
      ExecutionState.referenceFiberSum
        (run.finalState environment Reference original.state)
        (fun store _ => if read store = value then 1 else 0) left right =
      ExecutionState.referenceFiberSum
        (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
        (fun entry _ => ((kernel entry value).toReal : ℂ)) left right) :
    ((run.finalState environment Reference original.state).toPMF
      ((run.finalState_mass environment Reference original.state).trans
          original.normalized)).map read =
    ((original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))).toPMF
      (original.state.mapClassical_normalized original.normalized
        (fun entry => (entry.1, (entry.2, entry.1))))).bind kernel := by
  exact ExecutionState.toPMF_map_eq_bind_of_referenceFiberSum _ _ _ _ read kernel observed


end

end QuantumAlg.AlgorithmRun

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The real next-batch output state has the full conditional reference law,
with path histories projected away only after the paid factor readout. -/
lemma nextCompletedRun_finalState_reference {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextCompletedRun base noQuantum N input).finalState (sourceEnvironment input) Reference
        original.state)
      (fun store _ => weight
        (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum
      (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
            (Batch.SourceRecovery.packedValue output)))
      left right := by
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have enteredNormalized : entered.IsNormalized :=
    original.state.mapClassical_normalized original.normalized
      (fun entry => (entry.1, (entry.2, entry.1)))
  calc
    _ = ExecutionState.referenceFiberSum
          ((nextCompletedCode base noQuantum N input).execute (sourceEnvironment input)
            Reference entered)
          (fun entry _ => weight
            (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
          left right := by
            change ExecutionState.referenceFiberSum
              (((nextCompletedCode base noQuantum N input).execute (sourceEnvironment input)
                Reference entered).mapClassical
                Prod.fst)
              (fun store _ => weight
                (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
              left right = _
            exact ExecutionState.referenceFiberSum_mapClassical _ _ _ left right
    _ = _ := nextCompleted_reference base noQuantum N input entered enteredNormalized
      weight left right

/-- An indicator of the retained value turns the recovered source's complex
weight formula into the point mass of its actual PMF pushforward. -/
private lemma source_retained_point
    (selected value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (∑ output : (Batch.resultShape N).Value,
      ((Batch.sourceDistribution input output).toReal : ℂ) *
        (if Optional.retainValue selected
          (Batch.SourceRecovery.packedValue output) = value then 1 else 0)) =
      (((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
        (Optional.retainValue selected)) value).toReal : ℂ) := by
  let source : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue
  have packed := PMF.sum_map_toReal_mul
    (Batch.sourceDistribution input) (Batch.SourceRecovery.packedValue (N := N))
    (fun factor => if Optional.retainValue selected factor = value then 1 else 0)
  rw [Batch.SourceRecovery.sourceDistribution_map_packedValue input] at packed
  have retained := PMF.sum_map_toReal_mul source (Optional.retainValue selected)
    (fun factor => if factor = value then 1 else 0)
  exact packed.symm.trans (retained.symm.trans
    (PMF.sum_toReal_indicator (source.map (Optional.retainValue selected)) value))

/-- At the actual final store, one complete reused batch is the incoming
classical distribution bound to the independent recovered batch source. -/
lemma nextCompletedRun_finalState_distribution {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference) :
    (((nextCompletedRun base noQuantum N input).finalState (sourceEnvironment input) Reference
      original.state).toPMF
      (((nextCompletedRun base noQuantum N input).finalState_mass (sourceEnvironment input)
        Reference original.state).trans
        original.normalized)).map
      (fun store => store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)) =
    ((original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))).toPMF
      (original.state.mapClassical_normalized original.normalized
        (fun entry => (entry.1, (entry.2, entry.1))))).bind
      (fun entry =>
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
          (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
              entry.1))) := by
  apply AlgorithmRun.finalState_distribution_of_reference
    (nextCompletedRun base noQuantum N input) (sourceEnvironment input) original
    (fun store => store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
    (fun entry =>
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
        (Optional.retainValue
          (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)))
  intro value left right
  calc
    _ = ExecutionState.referenceFiberSum
        (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
        (fun entry _ => ∑ output : (Batch.resultShape N).Value,
          ((Batch.sourceDistribution input output).toReal : ℂ) *
            (if Optional.retainValue
              (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
              (Batch.SourceRecovery.packedValue output) = value then 1 else 0))
        left right :=
      nextCompletedRun_finalState_reference base noQuantum N input original
        (fun factor => if factor = value then 1 else 0) left right
    _ = _ := by
      apply congrArg
        (fun observed : (Store (Retry.context base noQuantum N) ×
            ((model N).HiddenState × Store (Retry.context base noQuantum N))) →
              (Retry.context base noQuantum N).register.Index → ℂ =>
          ExecutionState.referenceFiberSum
            (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
            observed left right)
      funext entry basis
      exact source_retained_point N input
        (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1) value

/-- The next batch's public factor output is the incoming caller/service PMF
bound to the independent recovered source with the old selector retained. -/
lemma nextCompletedRun_outputDistribution {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference) :
    (nextCompletedRun base noQuantum N input).outputDistribution (sourceEnvironment input)
      original =
      (original.state.toPMF original.normalized).bind (fun entry =>
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
          (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
              entry.1))) := by
  let run := nextCompletedRun base noQuantum N input
  let read (store : Store (Retry.context base noQuantum N)) :=
    store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)
  calc
    run.outputDistribution (sourceEnvironment input) original =
        ((run.finalState (sourceEnvironment input) Reference original.state).toPMF
          ((run.finalState_mass (sourceEnvironment input) Reference original.state).trans
            original.normalized)).map
          run.output.eval :=
      AlgorithmRun.outputDistribution_eq_finalState_read run (sourceEnvironment input) original
    _ = ((run.finalState (sourceEnvironment input) Reference original.state).toPMF
          ((run.finalState_mass (sourceEnvironment input) Reference original.state).trans
            original.normalized)).map
          read := by rfl
    _ = ((original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))).toPMF
          (original.state.mapClassical_normalized original.normalized
            (fun entry => (entry.1, (entry.2, entry.1))))).bind
          (fun entry =>
            ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
              (Optional.retainValue
                (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
                  entry.1))) :=
      nextCompletedRun_finalState_distribution base noQuantum N input original
    _ = _ := by
      rw [ExecutionState.toPMF_mapClassical, PMF.bind_map]
      rfl

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
