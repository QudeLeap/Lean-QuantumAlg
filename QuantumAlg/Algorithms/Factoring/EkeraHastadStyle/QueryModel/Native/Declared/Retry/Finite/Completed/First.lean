/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution.Moments

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.AllKeys
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Coordinates
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.First.Probability
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Readout

/-!
# The first completed EH batch and its direct cycle certificate

The first source draw, physical sample bank, recovery and retained selection
are followed by the actual result pack and physical reset. This is the first
segment of the completed schedule, with an independent one-batch contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The initialized first batch has its own concrete pack and terminal reset. -/
def firstCompletedAlgorithm (input : Input N) :
    Algorithm (model input) base (Retry.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run :=
    { code := ((Retry.first base noQuantum N input).seq
        ((Circuit.id (model := model input) (Retry.context base noQuantum N)).seq
          (Retry.pack base noQuantum N input))).seq (Cleanup.reset base noQuantum N input)
      output := Output.all (Retry.context base noQuantum N)
        (.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)) }

/-- The retained first-batch selector has the source law needed by the next real batch. -/
theorem firstCompleted_selected_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((firstCompletedAlgorithm base noQuantum input).run.code.execute Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            selected).toReal : ℂ) * weight selected)
        left right := by
  let head := Retry.first base noQuantum N input
  let identity := Circuit.id (model := model input) (Retry.context base noQuantum N)
  let packed := identity.seq (Retry.pack base noQuantum N input)
  let earlier := head.seq packed
  let entered := head.execute Reference state
  let observe := fun store : Store (Retry.context base noQuantum N) =>
    weight (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection store)
  have identityLaw :
      ExecutionState.referenceFiberSum (identity.execute Reference entered)
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum entered
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right := by
    rw [Circuit.execute_id_mapClassical (model := model input),
      ExecutionState.referenceFiberSum_mapClassical]
  have firstLaw := Retry.first_factor_reference base noQuantum N input
    state normalized weight left right
  have combined := (Circuit.referenceFiberSum_execute_seq earlier
    (Cleanup.reset base noQuantum N input) state observe left right).trans
      ((Cleanup.reset_reference base noQuantum N input
        (earlier.execute Reference state) observe left right).trans
        ((Circuit.referenceFiberSum_execute_seq head packed state observe left right).trans
          ((Circuit.referenceFiberSum_execute_seq identity (Retry.pack base noQuantum N input)
            entered observe left right).trans
            ((Cleanup.pack_selected_reference base noQuantum N input
              (identity.execute Reference entered) weight left right).trans
              (identityLaw.trans firstLaw)))))
  exact combined

/-- Every first-batch reference coefficient follows the independent source law. -/
theorem firstCompleted_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((firstCompletedAlgorithm base noQuantum input).run.code.execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((AllKeys.sourceDistribution input 1 selected).toReal : ℂ) * weight selected)
        left right := by
  let head := Retry.first base noQuantum N input
  let identity := Circuit.id (model := model input) (Retry.context base noQuantum N)
  let packed := identity.seq (Retry.pack base noQuantum N input)
  let earlier := head.seq packed
  let entered := head.execute Reference state
  let observe := fun store : Store (Retry.context base noQuantum N) =>
    weight (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
  have identityLaw :
      ExecutionState.referenceFiberSum (identity.execute Reference entered)
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum entered
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) left right := by
    rw [Circuit.execute_id_mapClassical (model := model input),
      ExecutionState.referenceFiberSum_mapClassical]
  have firstLaw := Retry.first_factor_reference base noQuantum N input
    state normalized weight left right
  have combined := (Circuit.referenceFiberSum_execute_seq earlier
    (Cleanup.reset base noQuantum N input) state observe left right).trans
      ((Cleanup.reset_reference base noQuantum N input
        (earlier.execute Reference state) observe left right).trans
        ((Circuit.referenceFiberSum_execute_seq head packed state observe left right).trans
          ((Circuit.referenceFiberSum_execute_seq identity (Retry.pack base noQuantum N input)
            entered observe left right).trans
            ((Retry.pack_reference base noQuantum N input
              (identity.execute Reference entered) weight left right).trans
              (identityLaw.trans firstLaw)))))
  refine combined.trans ?_
  apply congrArg (fun scalar : ℂ =>
    ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
  let distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue
  have zeroMoment (selected : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
      Optional.Distribution.moment distribution 0 selected weight = weight selected := by
    simp [Optional.Distribution.moment, PMF.independentReplicateVector, apply_ite]
  have oneMoment : Optional.Distribution.moment distribution 1 .optionNone weight =
      ∑ selected, ((distribution selected).toReal : ℂ) * weight selected := by
    simpa only [Optional.retainValue, zeroMoment] using
      (Optional.Distribution.moment_succ distribution 0 .optionNone weight)
  exact oneMoment.symm.trans (Optional.Distribution.moment_selected distribution 1 weight)

/-- The terminal physical reset establishes the complete zero bank after the first batch. -/
theorem firstCompleted_seeded (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History)) :
    BasisSeeded.Holds (Retry.context base noQuantum N).quantumLayout.zeroLabel
      ((firstCompletedAlgorithm base noQuantum input).run.code.execute Reference state) := by
  let earlier := (Retry.first base noQuantum N input).seq
    ((Circuit.id (model := model input) (Retry.context base noQuantum N)).seq
      (Retry.pack base noQuantum N input))
  apply BasisSeeded.seq earlier (Cleanup.reset base noQuantum N input)
  exact Cleanup.reset_seeded base noQuantum N input (earlier.execute Reference state)

/-- The first actual completed batch has the independent one-batch factor law. -/
theorem firstCompletedAlgorithm_sourceDistribution (input : Input N) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    (firstCompletedAlgorithm base noQuantum input).run.outputDistribution original =
      AllKeys.sourceDistribution input 1 := by
  let entered : State base Reference ((model input).HiddenState × Store base) :=
    original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum entered
    ((firstCompletedAlgorithm base noQuantum input).run.code.execute Reference entered)
    normalized
    (((firstCompletedAlgorithm base noQuantum input).run.code.execute_mass
      Reference entered).trans normalized)
    (fun entry => entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
    (AllKeys.sourceDistribution input 1)
  intro selected left right
  exact (firstCompleted_reference base noQuantum input entered normalized
    (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum entered (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator _ selected))

private theorem firstCompleted_joint_entry (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (left right : (Retry.context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((firstCompletedAlgorithm base noQuantum input).run.code.execute
      Reference state).mapClassical (fun entry =>
        (firstCompletedAlgorithm base noQuantum input).run.output.eval entry.1)).block value).matrix
          (left, leftRef) (right, rightRef) =
      if left = (Retry.context base noQuantum N).quantumLayout.zeroLabel ∧
          right = (Retry.context base noQuantum N).quantumLayout.zeroLabel then
        ((AllKeys.sourceDistribution input 1 value).toReal : ℂ) *
          state.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  exact BasisSeeded.readout_entry_of_reference
    (source := base) (ctx := Retry.context base noQuantum N) (Reference := Reference)
    (SourceHistory := (model input).HiddenState × History)
    (History := (model input).HiddenState ×
      (History × (firstCompletedAlgorithm base noQuantum input).run.code.Path))
    state ((firstCompletedAlgorithm base noQuantum input).run.code.execute Reference state)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    (firstCompleted_seeded base noQuantum input state)
    (firstCompletedAlgorithm base noQuantum input).run.output.eval
    (AllKeys.sourceDistribution input 1)
    (firstCompleted_reference base noQuantum input state normalized)
    value left right leftRef rightRef

private irreducible_def firstSealedRun (input : Input N) : AlgorithmRun (model input) base
    (Retry.context base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  (firstCompletedAlgorithm base noQuantum input).run

set_option Elab.async false in
private theorem firstSealed_statePromise (input : Input N) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed (Cleanup.stateTarget base noQuantum N original.caller)
      (Cleanup.stateTarget_normalized base noQuantum N original.caller)).Holds
      ((((firstSealedRun base noQuantum input).finalState Reference
        original.state).mapClassical (firstSealedRun base noQuantum input).output.eval).block
          value) := by
  apply AlgorithmRun.basisReference_readout_of_executionEntries
    (firstSealedRun base noQuantum input)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    (AllKeys.sourceDistribution input 1) _ original value
  intro reference history _ state normalized output left right leftRef rightRef
  rw [firstSealedRun_def]
  exact firstCompleted_joint_entry base noQuantum input
    state normalized output left right leftRef rightRef

/-- Every first-batch result has the complete zero-bank/reference state promise. -/
theorem firstCompleted_stateRequirement_holds (input : Input N) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    (Cleanup.stateRequirement base noQuantum N 1).Holds original.caller
      ((firstCompletedAlgorithm base noQuantum input).run.finalState
        Reference original.state) := by
  intro value
  have canonical := firstSealed_statePromise base noQuantum input original value
  rw [firstSealedRun_def] at canonical
  exact StatePromise.mixed_fullSelection
    (Retry.context base noQuantum N).quantumLayout Reference
    (Cleanup.stateTarget base noQuantum N original.caller)
    (Cleanup.stateTarget_normalized base noQuantum N original.caller) _ canonical

private theorem firstCompleted_relationalProbability (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    ((firstCompletedAlgorithm base noQuantum input).relationalDistribution
      original).toOuterMeasure
        {pair | (AllKeys.problem base noQuantum input 1 duration unitQueries).accepts
          pair.1 pair.2} = 1 - AllKeys.sourceFailure input ^ 1 := by
  have projection :
      ((firstCompletedAlgorithm base noQuantum input).relationalDistribution
        original).toOuterMeasure
          {pair | (AllKeys.problem base noQuantum input 1 duration unitQueries).accepts
            pair.1 pair.2} =
        ((firstCompletedAlgorithm base noQuantum input).run.outputDistribution
          original).toOuterMeasure (AllKeys.accepts N) := by
    simp only [Algorithm.relationalDistribution, AllKeys.problem,
      AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, firstCompletedAlgorithm_sourceDistribution]
  exact AllKeys.sourceDistribution_success input 1

/-- The first physical batch pays sixteen granted queries; its pack and reset add none. -/
theorem firstCompleted_query_count (input : Input N)
    (path : (firstCompletedAlgorithm base noQuantum input).run.code.Path) :
    ResourcePool.count (Cleanup.groupQuery N input)
      ((firstCompletedAlgorithm base noQuantum input).run.code.resourcePool path) = 16 := by
  change ResourcePool.count (Cleanup.groupQuery N input)
    ((Retry.first base noQuantum N input).resourcePool path.1.1 +
      (0 + ResourcePool.singleton (Retry.packEvent input)) +
        (Cleanup.reset base noQuantum N input).resourcePool path.2) = _
  simp only [ResourcePool.count_add, Cleanup.first_count, Cleanup.terminal_reset_zero,
    Retry.packEvent, ResourcePool.count_singleton,
    reduceCtorEq, if_false, add_zero, zero_add]

/-- The actual first segment pays its preparation, recovery, pack and reset. -/
theorem firstCompleted_resourcePool_le (input : Input N)
    (path : (firstCompletedAlgorithm base noQuantum input).run.code.Path) :
    (firstCompletedAlgorithm base noQuantum input).run.code.resourcePool path ≤
      Cleanup.eventBudget input 1 := by
  change (Retry.first base noQuantum N input).resourcePool path.1.1 +
    (0 + ResourcePool.singleton (Retry.packEvent input)) +
      (Cleanup.reset base noQuantum N input).resourcePool path.2 ≤ _
  simpa only [Cleanup.eventBudget, Finite.eventBudget, Retry.eventBudget,
    ResourcePool.scale_zero] using
    add_le_add
      (add_le_add (Retry.first_pool base noQuantum N input path.1.1) le_rfl)
      (Cleanup.reset_pool base noQuantum N input path.2)

/-- The whole first segment keeps every serial dependency under an arbitrary event clock. -/
theorem firstCompleted_depth_le (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (path : (firstCompletedAlgorithm base noQuantum input).run.code.Path) :
    (firstCompletedAlgorithm base noQuantum input).run.code.depth duration path ≤
      Cleanup.durationBudget input duration 1 := by
  change (Retry.first base noQuantum N input).depth duration path.1.1 +
    (0 + duration (Retry.packEvent input)) +
      (Cleanup.reset base noQuantum N input).depth duration path.2 ≤ _
  simpa only [Cleanup.durationBudget, Finite.durationBudget, Retry.durationBudget,
    Nat.zero_mul] using
    Nat.add_le_add
      (Nat.add_le_add (Retry.first_depth base noQuantum N input duration path.1.1) le_rfl)
      (Cleanup.reset_depth base noQuantum N input duration path.2)

/-- The first segment's pack uses the existing bank and fixed retained cells. -/
theorem firstCompleted_peakResidentSpace_le (input : Input N)
    (path : (firstCompletedAlgorithm base noQuantum input).run.code.Path) :
    (firstCompletedAlgorithm base noQuantum input).run.code.peakResidentSpace path ≤
      additionalSpace N 1 + base.residentSpace := by
  change _ ≤ Retry.additionalSpace N + base.residentSpace
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact Retry.first_resident base noQuantum N input path.1.1
    · refine (Circuit.peakResidentSpace_seq _ _ path.1.2).le.trans (SpacePool.max_le ?_ ?_)
      · exact (Circuit.peakResidentSpace_id path.1.2.1).trans_le
          (Retry.context_resident_allowance base noQuantum N)
      · have packed : (Retry.pack base noQuantum N input).peakResidentSpace path.1.2.2 =
            (Retry.context base noQuantum N).residentSpace := by
          funext axis
          exact Nat.max_zero _
        exact packed.trans_le (Retry.context_resident_allowance base noQuantum N)
  · exact Cleanup.reset_resident base noQuantum N input path.2

/-- The same concrete first segment respects the caller's separate auxiliary role. -/
theorem firstCompleted_peakAuxiliarySpace_le (input : Input N)
    (path : (firstCompletedAlgorithm base noQuantum input).run.code.Path) :
    (firstCompletedAlgorithm base noQuantum input).run.code.peakAuxiliarySpace path ≤
      additionalSpace N 1 + base.auxiliarySpace := by
  change _ ≤ Retry.additionalSpace N + base.auxiliarySpace
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact Retry.first_auxiliary base noQuantum N input path.1.1
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1.2).le.trans (SpacePool.max_le ?_ ?_)
      · exact (Circuit.peakAuxiliarySpace_id path.1.2.1).trans_le
          (Retry.context_auxiliary_allowance base noQuantum N)
      · have packed : (Retry.pack base noQuantum N input).peakAuxiliarySpace path.1.2.2 =
            (Retry.context base noQuantum N).auxiliarySpace := by
          funext axis
          exact Nat.max_zero _
        exact packed.trans_le (Retry.context_auxiliary_allowance base noQuantum N)
  · exact Cleanup.reset_auxiliary base noQuantum N input path.2

/-- The first completed segment satisfies every source, joint state, restoration
and resource obligation of its own one-batch protocol. -/
theorem firstCompletedAlgorithm_solves (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.Solves (firstCompletedAlgorithm base noQuantum input)
      (AllKeys.problem base noQuantum input 1 duration unitQueries) := by
  constructor
  · intro Reference original _valid _initialized
    exact le_of_eq
      (firstCompleted_relationalProbability base noQuantum input duration
        unitQueries original).symm
  · intro Reference original _valid _initialized requirement present
    have same : requirement = Cleanup.stateRequirement base noQuantum N 1 :=
      List.mem_singleton.mp present
    subst requirement
    exact firstCompleted_stateRequirement_holds base noQuantum input original
  · intro Reference original _valid _initialized
    have empty : base.borrowedQuantumWires = [] := by
      have subset := base.borrowedQuantumWires_sublist
      rw [noQuantum] at subset
      exact List.sublist_nil.mp subset
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (firstCompletedAlgorithm base noQuantum input).run.code empty reference state
  · intro _Reference _original _valid _initialized path _supported
    exact firstCompleted_resourcePool_le base noQuantum input path
  · intro _Reference _original _valid _initialized path _supported
    exact firstCompleted_peakResidentSpace_le base noQuantum input path
  · intro _Reference _original _valid _initialized path _supported
    exact firstCompleted_peakAuxiliarySpace_le base noQuantum input path
  · intro _Reference _original _valid _initialized path _supported
    exact firstCompleted_depth_le base noQuantum input duration path

/-- The first completed segment ends with a measured and jointly restored zero-bank boundary. -/
theorem firstCompleted_restartCleanup (input : Input N) :
    Circuit.RestartCleanup (firstCompletedAlgorithm base noQuantum input).run.code where
  measured := by
    intro path
    obtain ⟨dimension, present⟩ := Cleanup.reset_measured base noQuantum N input path.2
    exact ⟨dimension, List.mem_append.mpr (Or.inr present)⟩
  restores := by
    intro Reference History _ state
    have empty : base.borrowedQuantumWires = [] := by
      have subset := base.borrowedQuantumWires_sublist
      rw [noQuantum] at subset
      exact List.sublist_nil.mp subset
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (firstCompletedAlgorithm base noQuantum input).run.code empty Reference state
  reinitialized := by
    refine ⟨(Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis
      (Retry.context base noQuantum N).borrowedSelectionᶜ
      (Retry.context base noQuantum N).quantumLayout.zeroLabel, ?_⟩
    intro Reference History _ state label
    exact Cleanup.seeded_recordSeed _ _
      (firstCompleted_seeded base noQuantum input state) label
      (Retry.context base noQuantum N).borrowedSelectionᶜ

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
