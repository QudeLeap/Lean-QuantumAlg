/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Distribution
import all QuantumAlg.Core.Execution.Input.Successor.Distribution

/-!
# The actual reused batch supplies the next cycle's entry domain

The selector after one further paid batch is the incoming selector retained
against the independent recovered source. This conditional law, together with
the source's factor soundness, preserves the local admission domain without
assuming independence of the incoming caller, service and reference state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private lemma source_retained_selector_point
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

set_option maxHeartbeats 600000 in
-- The conditional finite-kernel bridge elaborates the complete selected
-- circuit once; no circuit definition is expanded in the support argument.
/-- The retained selector in the actual next input follows the full
input-dependent first-success kernel, after only paths are forgotten. -/
lemma nextCompleted_nextInput_selectedDistribution {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference) :
    ((((nextCompletedCode base noQuantum N input).nextInput (sourceEnvironment input)
      original).state.toPMF
      ((nextCompletedCode base noQuantum N input).nextInput (sourceEnvironment input)
        original).normalized).map
        (fun entry => Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) =
      (original.state.toPMF original.normalized).bind (fun entry =>
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
          (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
              entry.1))) := by
  let code := nextCompletedCode base noQuantum N input
  let selected (store : Store (Retry.context base noQuantum N)) :=
    Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection store
  let source : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))
  have enteredNormalized : entered.IsNormalized :=
    original.state.mapClassical_normalized original.normalized
      (fun entry => (entry.1, (entry.2, ())))
  let final := code.execute (sourceEnvironment input) Reference entered
  have finalNormalized : final.IsNormalized :=
    (code.execute_mass (sourceEnvironment input) Reference entered).trans enteredNormalized
  let kernel (entry : Store (Retry.context base noQuantum N) ×
      ((model N).HiddenState × Unit)) :=
    source.map (Optional.retainValue (selected entry.1))
  have law : (final.toPMF finalNormalized).map (fun record => selected record.1) =
      (entered.toPMF enteredNormalized).bind kernel := by
    apply ExecutionState.toPMF_map_eq_bind_of_referenceFiberSum
      entered final enteredNormalized finalNormalized
        (fun record => selected record.1) kernel
    intro value left right
    calc
      _ = ExecutionState.referenceFiberSum entered
          (fun entry _ => ∑ output : (Batch.resultShape N).Value,
            ((Batch.sourceDistribution input output).toReal : ℂ) *
              (if Optional.retainValue (selected entry.1)
                (Batch.SourceRecovery.packedValue output) = value then 1 else 0))
          left right :=
        nextCompleted_selected_reference base noQuantum N input entered
          enteredNormalized (fun observed => if observed = value then 1 else 0)
          left right
      _ = _ := by
        apply congrArg
          (fun observed : (Store (Retry.context base noQuantum N) ×
              ((model N).HiddenState × Unit)) →
                (Retry.context base noQuantum N).register.Index → ℂ =>
            ExecutionState.referenceFiberSum entered observed left right)
        funext entry basis
        exact source_retained_selector_point N input (selected entry.1) value
  calc
    _ = (final.toPMF finalNormalized).map (fun record => selected record.1) :=
      Circuit.nextInput_readoutDistribution code (sourceEnvironment input) original selected
    _ = (entered.toPMF enteredNormalized).bind kernel := law
    _ = _ := by
      rw [ExecutionState.toPMF_mapClassical, PMF.bind_map]
      rfl

/-- Every admitted actual reused batch leaves a sound live selector for the
next independently specified batch, including arbitrary reference entanglement. -/
lemma nextCompleted_nextInput_selectedSound {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference)
    (admitted : selectedSound base noQuantum N original.localState) :
    selectedSound base noQuantum N
      ((nextCompletedCode base noQuantum N input).nextInput (sourceEnvironment input)
        original).localState := by
  intro record word positive selected
  have supported := Circuit.nextInput_local_readout_support
    (nextCompletedCode base noQuantum N input) (sourceEnvironment input) original
    (fun store => Optional.selectedValue
      (Retry.selectionRefs base noQuantum N).selection store)
    record positive
  rw [nextCompleted_nextInput_selectedDistribution base noQuantum N input original]
    at supported
  rw [selected] at supported
  obtain ⟨entry, entrySupported, retainedSupported⟩ :=
    (PMF.mem_support_bind_iff (original.state.toPMF original.normalized)
      (fun entry =>
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
          (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
              entry.1))) (.optionSome word)).1 supported
  obtain ⟨factor, factorSupported, retained⟩ :=
    (PMF.mem_support_map_iff
      (Optional.retainValue
        (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
          entry.1))
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
      (.optionSome word)).1 retainedSupported
  cases hprevious : Optional.selectedValue
      (Retry.selectionRefs base noQuantum N).selection entry.1 with
  | optionNone =>
      have factorSome : factor = .optionSome word := by
        simpa only [hprevious, Optional.retainValue] using retained
      subst factor
      exact Batch.Recovery.sourceOutput_some_sound N input word factorSupported
  | optionSome prior =>
      have priorEq : prior = word := by
        simpa only [hprevious, Optional.retainValue, CShape.Value.optionSome.injEq]
          using retained
      subst prior
      have jointPositive : 0 < (original.state.block entry).mass :=
        (ExecutionState.mem_support_toPMF_iff original.state original.normalized entry).1
          entrySupported
      have localPositive : 0 < (original.localState.block entry).mass := by
        simpa only [OracleInput.oracleInput_localState_block,
          DensityOperator.marginalLeft_mass] using jointPositive
      exact admitted entry word localPositive hprevious

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
