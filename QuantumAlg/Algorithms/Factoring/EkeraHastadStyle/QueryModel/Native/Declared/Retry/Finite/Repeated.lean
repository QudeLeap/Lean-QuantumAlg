/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution.Moments

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.First
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.State.Readout

/-!
# Chronological source law across physically completed EH batches

The first batch and every later batch each execute their own paid pack and
physical reset. The selector stays live between them. These direct laws
retain the complete external-reference matrix and arbitrary incoming
service state, with no good-key assumption. The completed algorithm consumes
this same chronological code and its state and resource theorems.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)
variable {environment : (model N).Environment}

/-- The actual same-bank repetition of independently completed later batches. -/
def laterCompletedCode (count : Nat) : Circuit (model N)
    (Retry.context base noQuantum N) (Retry.context base noQuantum N) :=
  Circuit.forRange count (fun _ => nextCompletedCode base noQuantum N input)

/-- The directly completed first batch followed by exactly the requested number of
further independently completed batches. -/
def completedCode (laterCount : Nat) : Circuit (model N) base
    (Retry.context base noQuantum N) :=
  ((firstCompletedAlgorithm base noQuantum input).run.code).seq
    (laterCompletedCode base noQuantum N input laterCount)

/-- The physically completed schedule reads the original retained factor
destination and lists the same complete live store and bank. -/
def completedRun (laterCount : Nat) : AlgorithmRun (model N) base
    (Retry.context base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N) where
  code := completedCode base noQuantum N input laterCount
  output := Output.all (Retry.context base noQuantum N)
    (.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))

lemma completedRun_code (laterCount : Nat) :
    (completedRun base noQuantum N input laterCount).code =
      completedCode base noQuantum N input laterCount := rfl

/-- Each actual later segment resets the original bank to one fixed seed,
independently of its incoming store, service state, quantum state and reference. -/
lemma nextCompleted_seeded {Reference : Register} {History : Type}
    [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model N).HiddenState × History)) :
    BasisSeeded.Holds (Retry.context base noQuantum N).quantumLayout.zeroLabel
      ((nextCompletedCode base noQuantum N input).execute environment Reference state) := by
  let earlier := (Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N)
  change BasisSeeded.Holds (Retry.context base noQuantum N).quantumLayout.zeroLabel
    ((earlier.seq (reset base noQuantum N)).execute environment Reference state)
  apply BasisSeeded.seq earlier (reset base noQuantum N) environment
  exact reset_seeded base noQuantum N (earlier.execute environment Reference state)

/-- Zero further batches preserve the first cleanup seed; every actual
further batch reestablishes it at its own terminal reset. -/
lemma laterCompleted_seeded (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (incoming : BasisSeeded.Holds
      (Retry.context base noQuantum N).quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (Retry.context base noQuantum N).quantumLayout.zeroLabel
      ((laterCompletedCode base noQuantum N input count).execute environment Reference state) := by
  induction count generalizing History with
  | zero =>
      change BasisSeeded.Holds
        (Retry.context base noQuantum N).quantumLayout.zeroLabel
        ((Circuit.id (model := model N) (Retry.context base noQuantum N)).execute environment
          Reference state)
      rw [Circuit.execute_id_mapClassical (model := model N)]
      have sameHistory :
          state.mapHistory (fun history => (history.1, (history.2, ()))) =
            state.mapClassical
              (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
        unfold State.mapHistory
        exact ExecutionState.executionState_mapClassical_congr_decision
          state _ _ (fun _ => rfl) _ _
      rw [← sameHistory]
      exact BasisSeeded.mapHistory _ state incoming _
  | succ count ih =>
      let head := nextCompletedCode base noQuantum N input
      let tail := laterCompletedCode base noQuantum N input count
      have seeded := nextCompleted_seeded (environment := environment) base noQuantum N input state
      have later := ih (head.execute environment Reference state) seeded
      exact BasisSeeded.seq head tail environment _ state later

/-- The first real cleanup and every later reset leave the same all-zero
owned bank seed on the final complete execution state. -/
lemma completed_seeded (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History)) :
    BasisSeeded.Holds (Retry.context base noQuantum N).quantumLayout.zeroLabel
      ((completedCode base noQuantum N input laterCount).execute environment Reference state) := by
  let first := (firstCompletedAlgorithm base noQuantum input).run.code
  let tail := laterCompletedCode base noQuantum N input laterCount
  have firstSeed := firstCompleted_seeded (environment := environment) base noQuantum input state
  have later := laterCompleted_seeded (environment := environment) base noQuantum N input laterCount
    (first.execute environment Reference state) firstSeed
  exact BasisSeeded.seq first tail environment _ state later

private lemma nextCompleted_factor_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextCompletedCode base noQuantum N input).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          factor).toReal : ℂ) *
          weight (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
            factor)) left right := by
  refine (nextCompleted_selected_reference base noQuantum N input state normalized
    weight left right).trans ?_
  apply congrArg
    (fun observed : (Store (Retry.context base noQuantum N) ×
        ((model N).HiddenState × History)) →
          (Retry.context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observed left right)
  funext entry basis
  have pushed := PMF.sum_map_toReal_mul
    (Batch.sourceDistribution input) (Batch.SourceRecovery.packedValue (N := N))
    (fun factor => weight (Optional.retainValue
      (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
      factor))
  rw [Batch.SourceRecovery.sourceDistribution_map_packedValue input] at pushed
  exact pushed.symm

/-- Every real later completed batch advances the same chronological
first-success moment, for arbitrary normalized store/service/reference input. -/
lemma laterCompleted_selected_reference (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((laterCompletedCode base noQuantum N input count).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => Optional.Distribution.moment
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        count (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1) weight)
      left right := by
  induction count generalizing History with
  | zero =>
      change ExecutionState.referenceFiberSum
        ((Circuit.id (model := model N) (Retry.context base noQuantum N)).execute
          (sourceEnvironment input) Reference state)
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right = _
      rw [Circuit.execute_id_mapClassical (model := model N)]
      rw [ExecutionState.referenceFiberSum_mapClassical]
      simp [Optional.Distribution.moment, PMF.independentReplicateVector, apply_ite]
  | succ count ih =>
      let head := nextCompletedCode base noQuantum N input
      let tail := laterCompletedCode base noQuantum N input count
      have later := ih (head.execute (sourceEnvironment input) Reference state)
        ((head.execute_mass (sourceEnvironment input) Reference state).trans normalized)
      have earlier := nextCompleted_factor_reference base noQuantum N input
        state normalized
        (fun selected => Optional.Distribution.moment
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          count selected weight) left right
      refine (Circuit.referenceFiberSum_execute_seq head tail (sourceEnvironment input) state
        (fun store => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection store))
        left right).trans (later.trans (earlier.trans ?_))
      apply congrArg
        (fun observed : (Store (Retry.context base noQuantum N) ×
            ((model N).HiddenState × History)) →
              (Retry.context base noQuantum N).register.Index → ℂ =>
          ExecutionState.referenceFiberSum state observed left right)
      funext entry basis
      exact (Optional.Distribution.moment_succ _ count _ weight).symm

/-- The selector of the actual first-plus-repeated completed execution has
the original independent chronological source law at every positive count. -/
lemma completed_selected_reference (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => Optional.Distribution.moment
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        (laterCount + 1) .optionNone weight)
      left right := by
  let firstCode := (firstCompletedAlgorithm base noQuantum input).run.code
  let laterCode := laterCompletedCode base noQuantum N input laterCount
  let distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map (LatticeBatchRecoveryOutput.outputValue (N := N))
  let laterWeight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ :=
    fun selected => Optional.Distribution.moment distribution laterCount selected weight
  have combined :=
    (Circuit.referenceFiberSum_execute_seq firstCode laterCode (sourceEnvironment input) state
      (fun store => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection store)) left right).trans
      ((laterCompleted_selected_reference base noQuantum N input laterCount
        (firstCode.execute (sourceEnvironment input) Reference state)
        ((firstCode.execute_mass (sourceEnvironment input) Reference state).trans normalized)
        weight left right).trans
          (firstCompleted_selected_reference base noQuantum input state normalized
            laterWeight left right))
  refine combined.trans ?_
  apply congrArg
    (fun scalar : ℂ => ExecutionState.referenceFiberSum state
      (fun _ _ => scalar) left right)
  simpa only [laterWeight, Optional.retainValue] using
    (Optional.Distribution.moment_succ distribution laterCount .optionNone weight).symm

/-- The directly completed first batch stores exactly the persistent
selected value in the paid factor cell, in every weighted reference entry. -/
lemma oneCompleted_factor_selected_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((firstCompletedAlgorithm base noQuantum input).run.code).execute (sourceEnvironment
        input) Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum
      (((firstCompletedAlgorithm base noQuantum input).run.code).execute (sourceEnvironment
        input) Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right := by
  let distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map (LatticeBatchRecoveryOutput.outputValue (N := N))
  have factorLaw := firstCompleted_reference base noQuantum input state normalized
    weight left right
  have selectedLaw := firstCompleted_selected_reference base noQuantum input
    state normalized weight left right
  have zeroMoment (selected : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
      Optional.Distribution.moment distribution 0 selected weight = weight selected := by
    simp [Optional.Distribution.moment, PMF.independentReplicateVector, apply_ite]
  have firstMoment :
      Optional.Distribution.moment distribution 1 .optionNone weight =
        ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((distribution factor).toReal : ℂ) * weight factor := by
    simpa only [Optional.retainValue, zeroMoment] using
      (Optional.Distribution.moment_succ distribution 0 .optionNone weight)
  have sums :
      (∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((Optional.Distribution.selectedDistribution distribution 1 selected).toReal : ℂ) *
          weight selected) =
      ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((distribution factor).toReal : ℂ) * weight factor :=
    (Optional.Distribution.moment_selected distribution 1 weight).symm.trans firstMoment
  exact factorLaw.trans ((congrArg (fun scalar : ℂ =>
    ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right) sums).trans
      selectedLaw.symm)

/-- The paid pack in each later completed batch makes its final factor cell
and persistent selector observationally identical, including off-diagonal
reference coefficients. -/
lemma nextCompleted_factor_selected_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextCompletedCode base noQuantum N input).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum
      ((nextCompletedCode base noQuantum N input).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right :=
  (nextCompleted_reference base noQuantum N input state normalized weight left right).trans
    (nextCompleted_selected_reference base noQuantum N input state normalized
      weight left right).symm

/-- Equality of the paid factor cell and the persistent selector survives
any number of actual further completed batches. The zero case preserves the
incoming relation; every positive step reestablishes it by its own pack. -/
lemma laterCompleted_factor_selected_reference (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index)
    (incoming : ExecutionState.referenceFiberSum state
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right) :
    ExecutionState.referenceFiberSum
      ((laterCompletedCode base noQuantum N input count).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum
      ((laterCompletedCode base noQuantum N input count).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right := by
  induction count generalizing History with
  | zero =>
      change ExecutionState.referenceFiberSum
        ((Circuit.id (model := model N) (Retry.context base noQuantum N)).execute
          (sourceEnvironment input) Reference state)
        (fun entry _ => weight
          (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
        left right = ExecutionState.referenceFiberSum
          ((Circuit.id (model := model N) (Retry.context base noQuantum N)).execute
            (sourceEnvironment input) Reference state)
          (fun entry _ => weight (Optional.selectedValue
            (Retry.selectionRefs base noQuantum N).selection entry.1)) left right
      simp only [Circuit.execute_id_mapClassical (model := model N)]
      simp only [ExecutionState.referenceFiberSum_mapClassical]
      exact incoming
  | succ count ih =>
      let head := nextCompletedCode base noQuantum N input
      let tail := laterCompletedCode base noQuantum N input count
      have first := nextCompleted_factor_selected_reference base noQuantum N input
        state normalized weight left right
      have later := ih (head.execute (sourceEnvironment input) Reference state)
        ((head.execute_mass (sourceEnvironment input) Reference state).trans normalized) first
      exact (Circuit.referenceFiberSum_execute_seq head tail (sourceEnvironment input) state
        (fun store => weight
          (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
        left right).trans
        (later.trans
          (Circuit.referenceFiberSum_execute_seq head tail (sourceEnvironment input) state
            (fun store => weight (Optional.selectedValue
              (Retry.selectionRefs base noQuantum N).selection store))
            left right).symm)

/-- Every real completed finite repetition stores its selected factor in the
original result cell, without adding a redundant terminal pack. -/
lemma completed_factor_selected_reference (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum
      ((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right := by
  let first := (firstCompletedAlgorithm base noQuantum input).run.code
  let tail := laterCompletedCode base noQuantum N input laterCount
  have initial := oneCompleted_factor_selected_reference base noQuantum N input
    state normalized weight left right
  have later := laterCompleted_factor_selected_reference base noQuantum N input
    laterCount (first.execute (sourceEnvironment input) Reference state)
    ((first.execute_mass (sourceEnvironment input) Reference state).trans normalized) weight
      left right initial
  exact (Circuit.referenceFiberSum_execute_seq first tail (sourceEnvironment input) state
    (fun store => weight
      (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
    left right).trans
    (later.trans
      (Circuit.referenceFiberSum_execute_seq first tail (sourceEnvironment input) state
        (fun store => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection store))
        left right).symm)

/-- The final original result cell of every physically completed finite
execution has the same independent chronological first-success distribution
as the unchanged scientific source law, including exceptional inputs. -/
lemma completed_reference (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
        Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((Optional.Distribution.selectedDistribution
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          (laterCount + 1) selected).toReal : ℂ) * weight selected) left right := by
  let distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map (LatticeBatchRecoveryOutput.outputValue (N := N))
  exact (completed_factor_selected_reference base noQuantum N input laterCount
    state normalized weight left right).trans
      ((completed_selected_reference base noQuantum N input laterCount
        state normalized weight left right).trans
        (congrArg (fun scalar : ℂ => ExecutionState.referenceFiberSum state
          (fun _ _ => scalar) left right)
          (Optional.Distribution.moment_selected distribution (laterCount + 1) weight)))

/-- The actual all-input output PMF of the repeatedly completed execution
is the unchanged independent first-success law. -/
lemma completed_outputDistribution (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (completedRun base noQuantum N input laterCount).outputDistribution (sourceEnvironment
      input) original =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        (laterCount + 1) := by
  let entered : State base Reference ((model N).HiddenState × Store base) :=
    original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum entered
    ((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
      Reference entered)
    normalized
    (((completedCode base noQuantum N input laterCount).execute_mass (sourceEnvironment input)
      Reference entered).trans
      normalized)
    (fun entry => entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
    (Optional.Distribution.selectedDistribution
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
      (laterCount + 1))
  intro selected left right
  exact (completed_reference base noQuantum N input laterCount entered normalized
    (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum entered (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator _ selected))

/-- Every actual factor-output block has the complete zero-bank/reference
matrix dictated by the original all-input first-success law. No service or
path branch is assumed away: those labels are summed only at this readout. -/
lemma completed_joint_entry (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (left right : (Retry.context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
      Reference state).mapClassical
      (fun entry => (completedRun base noQuantum N input laterCount).output.eval entry.1)).block
        value).matrix (left, leftRef) (right, rightRef) =
      if left = (Retry.context base noQuantum N).quantumLayout.zeroLabel ∧
          right = (Retry.context base noQuantum N).quantumLayout.zeroLabel then
        ((Optional.Distribution.selectedDistribution
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          (laterCount + 1) value).toReal : ℂ) *
            state.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  exact BasisSeeded.readout_entry_of_reference
    (source := base) (ctx := Retry.context base noQuantum N) (Reference := Reference)
    (SourceHistory := (model N).HiddenState × History)
    (History := (model N).HiddenState ×
      (History × (completedCode base noQuantum N input laterCount).Path))
    state ((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
      Reference state)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    (completed_seeded base noQuantum N input laterCount state)
    (completedRun base noQuantum N input laterCount).output.eval
    (Optional.Distribution.selectedDistribution
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
      (laterCount + 1))
    (completed_reference base noQuantum N input laterCount state normalized)
    value left right leftRef rightRef

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
