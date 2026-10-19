/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.First
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Repeated
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources

/-!
# Two canonical completed EH batches

The canonical first-plus-one-reused execution preserves the explicit
chronological two-source reference law. Both real packs and physical resets
remain in its event and serial-depth budgets, while the maximum of its two
actual complete segment depths has the separate maximum allowance.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private lemma sourceWeight_eq
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ) :
    (∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
      ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        selected).toReal : ℂ) * weight selected) =
    ∑ source : (Batch.resultShape N).Value,
      ((Batch.sourceDistribution input source).toReal : ℂ) *
        weight (Batch.SourceRecovery.packedValue source) := by
  have pushed := PMF.sum_map_toReal_mul
    (Batch.sourceDistribution input) (Batch.SourceRecovery.packedValue (N := N)) weight
  rw [Batch.SourceRecovery.sourceDistribution_map_packedValue input] at pushed
  exact pushed

private lemma sourceWeight_reference {Reference : Register} {History : Type}
    [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          selected).toReal : ℂ) * weight selected) left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ source : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input source).toReal : ℂ) *
          weight (Batch.SourceRecovery.packedValue source)) left right :=
  congrArg (fun scalar : ℂ =>
    ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
    (sourceWeight_eq N input weight)

/-- Two canonical completed batches obey the full chronological two-source law
at every external-reference matrix coefficient. -/
lemma completedTwo_reference {Reference : Register} {History : Type}
    [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((completedCode base noQuantum N input 1).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ first : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input first).toReal : ℂ) *
          ∑ second : (Batch.resultShape N).Value,
            ((Batch.sourceDistribution input second).toReal : ℂ) *
              weight (Optional.retainValue
                (Batch.SourceRecovery.packedValue first)
                (Batch.SourceRecovery.packedValue second)))
      left right := by
  let firstCode := (firstCompletedAlgorithm base noQuantum input).run.code
  let nextCode := nextCompletedCode base noQuantum N input
  let identity := Circuit.id (allowAllocation := true) (model := model N)
    (Retry.context base noQuantum N)
  let tailCode := nextCode.seq identity
  let entered := firstCode.execute (sourceEnvironment input) Reference state
  let observed : Store (Retry.context base noQuantum N) → ℂ :=
    fun store => weight
      (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
  let nextWeight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ :=
    fun selected => ∑ second : (Batch.resultShape N).Value,
      ((Batch.sourceDistribution input second).toReal : ℂ) *
        weight (Optional.retainValue selected (Batch.SourceRecovery.packedValue second))
  have identityLaw :
      ExecutionState.referenceFiberSum
        (identity.execute (sourceEnvironment input) Reference (nextCode.execute
          (sourceEnvironment input) Reference entered))
        (fun entry _ => observed entry.1) left right =
      ExecutionState.referenceFiberSum (nextCode.execute (sourceEnvironment input) Reference
        entered)
        (fun entry _ => observed entry.1) left right := by
    rw [Circuit.execute_id_mapClassical (model := model N),
      ExecutionState.referenceFiberSum_mapClassical]
  calc
    _ = ExecutionState.referenceFiberSum (tailCode.execute (sourceEnvironment input) Reference
      entered)
        (fun entry _ => observed entry.1) left right :=
      Circuit.referenceFiberSum_execute_seq firstCode tailCode (sourceEnvironment input) state
        observed left right
    _ = ExecutionState.referenceFiberSum (nextCode.execute (sourceEnvironment input) Reference
      entered)
        (fun entry _ => observed entry.1) left right :=
      (Circuit.referenceFiberSum_execute_seq nextCode identity (sourceEnvironment input) entered
        observed
        left right).trans identityLaw
    _ = ExecutionState.referenceFiberSum entered
        (fun entry _ => nextWeight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right :=
      nextCompleted_reference base noQuantum N input entered
        ((firstCode.execute_mass (sourceEnvironment input) Reference state).trans normalized)
          weight left right
    _ = ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            selected).toReal : ℂ) * nextWeight selected) left right :=
      firstCompleted_selected_reference base noQuantum input state normalized
        nextWeight left right
    _ = _ := sourceWeight_reference base N input state nextWeight left right

/-- The canonical two-batch path pays both independently completed event pools. -/
lemma completedTwo_resourcePool_le
    (path : (completedCode base noQuantum N input 1).Path) :
    (completedCode base noQuantum N input 1).resourcePool path ≤
      twoCompletedEventBudget N := by
  have budgetEq : completedEventBudget N 1 = twoCompletedEventBudget N := by
    unfold completedEventBudget twoCompletedEventBudget
    rw [ResourcePool.scale, one_nsmul]
  exact (completed_resourcePool_le base noQuantum N input 1 path).trans_eq budgetEq

/-- The same canonical path retains the sum of both complete serial depths. -/
lemma completedTwo_depth_le (duration : Resource.Event (model N) → Nat)
    (path : (completedCode base noQuantum N input 1).Path) :
    (completedCode base noQuantum N input 1).depth duration path ≤
      twoCompletedDurationBudget N duration := by
  have budgetEq : completedDurationBudget N 1 duration =
      twoCompletedDurationBudget N duration := by
    unfold completedDurationBudget twoCompletedDurationBudget
    rw [Nat.one_mul]
  exact (completed_depth_le base noQuantum N input 1 duration path).trans_eq budgetEq

/-- The two actual complete segment depths obey their maximum allowance,
separately from the whole-run serial sum. -/
lemma completedTwo_maxBatchDepth_le (duration : Resource.Event (model N) → Nat)
    (path : (completedCode base noQuantum N input 1).Path) :
    max ((firstCompletedAlgorithm base noQuantum input).run.code.depth duration path.1)
      ((nextCompletedCode base noQuantum N input).depth duration path.2.1) ≤
        twoCompletedMaximumBatchBudget N duration := by
  exact max_le
    ((firstCompleted_depth_le base noQuantum input duration path.1).trans
      (le_max_left _ _))
    ((nextCompleted_depth_le base noQuantum N input duration path.2.1).trans
      (le_max_right _ _))

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
