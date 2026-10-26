/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Selected.Event
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Sampling
import all QuantumAlg.Core.Execution.Context.Embedding.References
import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Core.Execution.Composition.Laws

/-!
# Selected-frequency probability of the actual public allocating sampler

The actual public allocation is executed before the actual embedded reset and
converted stream. Splitting its result retains the complete public-frame Store
in History and the whole frame quantum factor beside external Reference. The
literal embedding execution rejoins every Store, service tag and allocation,
reset and stage Path. No independence or initialization premise is introduced.

The public observation reads the actual placed result cells. Pulling this
observation through the exact split/execute/join equation gives precisely the
child's original selected-frequency event. Consequently the existing one-round
floor holds for this actual public sampler on every subnormalized input. The checked-recovery
and finite-retry contracts have separate owners.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace Probability

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ECDLP.Measured
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth fourierModulus)
open _root_.QuantumAlg.FiniteCyclicDLP.Canonical.Probability (SecretInput)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma indicator_reindex {Records : Type} [Fintype Records]
    {Before After : Register} (state : ExecutionState Records Before)
    (coordinates : Before.Index ≃ After.Index) (event : Records → Prop) :
    (state.reindex coordinates).effectWeight (fun record => if event record then
      Effect.one After else Effect.zero After) =
      state.effectWeight (fun record => if event record then
        Effect.one Before else Effect.zero Before) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro record _
  by_cases observed : event record
  · simp only [if_pos observed, Effect.weight_one, ExecutionState.reindex_block_mass]
  · simp only [if_neg observed, Effect.weight_zero]

private lemma indicator_mapHistory {ctx : RuntimeCtx .quantum} {Reference : Register}
    {Before After : Type} [Fintype Before] [Fintype After]
    (state : State ctx Reference Before) (update : Before → After) (event : Store ctx → Prop) :
    (state.mapHistory update).effectWeight (fun record => if event record.1 then
      Effect.one (ctx.register.prod Reference) else Effect.zero (ctx.register.prod Reference)) =
      state.effectWeight (fun record => if event record.1 then
        Effect.one (ctx.register.prod Reference)
      else Effect.zero (ctx.register.prod Reference)) := by
  rw [State.mapHistory, ExecutionState.effectWeight_mapClassical_decision]

private lemma indicator_join {localCtx caller : RuntimeCtx .quantum}
    (placement : ContextEmbedding localCtx caller) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State localCtx (placement.frame.register.prod Reference)
      (Store placement.frame × History)) (event : Store caller × History → Prop) :
    (placement.join state).effectWeight (fun record => if event record then
      Effect.one (caller.register.prod Reference)
    else Effect.zero (caller.register.prod Reference)) =
      state.effectWeight (fun record => if event ((placement.record History).symm record) then
        Effect.one (localCtx.register.prod (placement.frame.register.prod Reference))
      else Effect.zero (localCtx.register.prod (placement.frame.register.prod Reference))) := by
  rw [ContextEmbedding.join, indicator_reindex, ExecutionState.effectWeight_mapClassical_decision]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

/-- Actual placement splits precisely the two original complete Store factors of the public union.
-/
lemma actual_placement_store :
    (AllocatedFixed.placement E m).store =
      ContextUnion.storeEquiv (Recovery.PublicInput.terminal_disjoint E m) := by
  apply Equiv.ext
  intro stored
  apply Prod.ext
  · apply Store.store_eq_of_storage_reads
    intro shape ref
    calc
      _ = stored.read ((AllocatedFixed.placement E m).input (.storage ref)) :=
        ((AllocatedFixed.placement E m).split_local_read stored (.storage ref)).symm
      _ = stored.read (ContextUnion.inputLeft (Recovery.PublicInput.terminal_disjoint E m)
          (.storage ref)) := by
        apply congrArg stored.read
        change CInputRef.storage _ = CInputRef.storage _
        apply congrArg CInputRef.storage
        exact CStorageRef.storageRef_eq_of_key _ _ rfl
      _ = _ := (TerminalStoreCoordinates.split_left_read
        (Recovery.PublicInput.terminal_disjoint E m) stored (.storage ref)).symm
  · apply Store.store_eq_of_storage_reads
    intro shape ref
    calc
      _ = stored.read ((AllocatedFixed.placement E m).unionFrameInput (.storage ref)) :=
        ((AllocatedFixed.placement E m).split_frame_read stored (.storage ref)).symm
      _ = stored.read (ContextUnion.inputRight (Recovery.PublicInput.terminal_disjoint E m)
          (.storage ref)) := by
        apply congrArg stored.read
        change CInputRef.storage _ = CInputRef.storage _
        apply congrArg CInputRef.storage
        exact CStorageRef.storageRef_eq_of_key _ _ rfl
      _ = _ := (TerminalStoreCoordinates.split_right_read
        (Recovery.PublicInput.terminal_disjoint E m) stored (.storage ref)).symm

/-- The original paired bits use existing caller result cells in their final coordinate order. -/
def readoutInput : CInputRef (Recovery.Layout.terminal p.size m) (.fixedVector (2 * m) (.finite
  2)) :=
  QubitReadouts.input (fun index => Recovery.Layout.resultCell p.size m
    (TerminalStoreCoordinates.blockReverse m index))

/-- Place those exact structural reads beside both resident borrowed public values. -/
def publicReadoutBits (stored : Store (Recovery.PublicInput.context E m)) : Fin (2 * m) → Bool :=
  QubitReadouts.mask (stored.read ((AllocatedFixed.placement E m).input (readoutInput (p := p) m)))

private lemma joined_publicReadoutBits (localStore : Store (Recovery.Layout.terminal p.size m))
    (frameStore : Store (AllocatedFixed.placement E m).frame) :
    publicReadoutBits E m ((AllocatedFixed.placement E m).store.symm (localStore, frameStore)) =
      SelectedObservation.readoutBits p m localStore := by
  rw [publicReadoutBits, ContextEmbedding.contextEmbedding_input_read]
  rfl

variable [Fact p.Prime] (fieldTail : Nat) (odd : Odd p) (seed : AffinePoint E)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Split any reused public caller without discarding its complete frame or older history. -/
def splitChildInput
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :=
  ((AllocatedFixed.placement E (orderWidth problem)).split state).mapClassical
    (fun record => (record.1, (record.2.2.1, (record.2.1, record.2.2.2))))

omit [Fact p.Prime] in
/-- The reused public caller and its exact complete child input have identical mass. -/
lemma splitChildInput_mass
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (splitChildInput E problem state).mass = state.mass := by
  rw [splitChildInput, ExecutionState.mapClassical_mass,
    ContextEmbedding.contextEmbedding_split_mass]

/-- The input to the actual fixed child retains the actual allocation Path and whole frame. -/
def allocatedChildInput
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :=
  splitChildInput E problem ((Allocation.circuit E (orderWidth problem)).execute environment
    Reference state)

omit [Fact p.Prime] in
/-- Neither actual allocation nor the full split/reordering changes the incoming mass. -/
lemma allocatedChildInput_mass
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (allocatedChildInput (environment := environment) E problem state).mass = state.mass := by
  rw [allocatedChildInput, splitChildInput_mass, Circuit.execute_mass]

set_option maxHeartbeats 400000 in
-- The complete execution equality needs a finite local elaboration budget.
/-- Literal public execution exposes the actual allocation, reset and converted stream together.

The three full record rearrangements retain every allocation, reset and stage Path.
-/
lemma actual_public_sampling_execute
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (Sampling.circuit E fieldTail (orderWidth problem) seed problem.order points
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
        Reference
        state =
      ((AllocatedFixed.placement E (orderWidth problem)).join
        ((((Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order points
          (Recovery.Layout.order (orderWidth problem))
            (GenericPointAddition.InPlace.Semantics.radixUnit
            p fieldTail.succ odd)).execute environment ((AllocatedFixed.placement E (orderWidth
              problem)).frame.register.prod Reference)
              ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
                environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
                Reference)
                (allocatedChildInput (environment := environment) E problem state))).mapHistory
                  (fun record =>
                  (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))).mapClassical
            (fun record =>
              (record.1, (record.2.2.1.1,
                (record.2.1, (record.2.2.1.2, record.2.2.2))))))).mapHistory
                  (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  dsimp only [allocatedChildInput, splitChildInput]
  rw [Sampling.circuit_execute, Circuit.circuit_execute_embed, Sampling.body_execute]
  dsimp only [State.mapHistory]
  apply Circuit.pushforward_congr
  apply congrArg ((AllocatedFixed.placement E (orderWidth problem)).join)
  apply Circuit.pushforward_congr
  apply Circuit.pushforward_congr
  apply congrArg ((Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order
    points (Recovery.Layout.order (orderWidth problem))
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
      ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference))
  apply congrArg ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
    environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference))
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The public event uses the actual placed final result-cell vector without packing. -/
def selectedEffects (input : SecretInput problem) (Reference : Register) {OutputHistory : Type} :
    Circuit.EffectFamily (Recovery.PublicInput.context E (orderWidth problem)) Reference
      OutputHistory :=
  fun record => if selectedExponentEvent problem input
    (publicReadoutBits E (orderWidth problem) record.1) = true then
      Effect.one ((Recovery.PublicInput.context E (orderWidth problem)).register.prod Reference)
    else Effect.zero ((Recovery.PublicInput.context E (orderWidth problem)).register.prod Reference)

set_option maxHeartbeats 400000 in
-- The complete embedded observation needs a finite local elaboration budget.
/-- Every complete reused public Store observation pulls back through the actual embedded body. -/
lemma actual_embedded_terminal_observation_weight
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (event : Store (Recovery.PublicInput.context E (orderWidth problem)) → Prop) :
    ((Circuit.embed (allowAllocation := false) (AllocatedFixed.placement E (orderWidth problem))
      (Sampling.body E fieldTail (orderWidth problem) seed problem.order points
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))).execute
          environment Reference state).effectWeight
        (fun record => if event record.1 then
          Effect.one ((Recovery.PublicInput.context E (orderWidth problem)).register.prod Reference)
        else Effect.zero ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
          Reference)) =
      ((Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order points
        (Recovery.Layout.order (orderWidth problem))
          (GenericPointAddition.InPlace.Semantics.radixUnit p
          fieldTail.succ odd)).execute environment ((AllocatedFixed.placement E (orderWidth
            problem)).frame.register.prod Reference)
            ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
              environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
              Reference)
              (splitChildInput E problem state))).effectWeight (fun record =>
                if event ((AllocatedFixed.placement E (orderWidth problem)).store.symm
                  (record.1, record.2.2.1.1.1)) then
                    Effect.one ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
                      ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
                        Reference))
                else Effect.zero ((Recovery.Layout.terminal p.size (orderWidth
                  problem)).register.prod
                  ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
                    Reference))) := by
  dsimp only [splitChildInput]
  erw [Circuit.circuit_execute_embed,
    indicator_join (Reference := Reference) (AllocatedFixed.placement E (orderWidth problem)),
    ExecutionState.effectWeight_mapClassical_decision,
    Sampling.body_execute, State.mapHistory, ExecutionState.effectWeight_mapClassical_decision]
  apply congrArg
  funext record
  rfl

set_option maxHeartbeats 800000 in
-- The complete embedded selected event needs a finite local elaboration budget.
/-- Reusing the complete dirty public caller gives exactly the actual child's selected weight. -/
lemma actual_embedded_selected_readout_weight
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (input : SecretInput problem) :
    ((Circuit.embed (allowAllocation := false) (AllocatedFixed.placement E (orderWidth problem))
      (Sampling.body E fieldTail (orderWidth problem) seed problem.order points
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))).execute
          environment Reference state).effectWeight
          (selectedEffects E problem input Reference) =
      ((Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order points
        (Recovery.Layout.order (orderWidth problem))
          (GenericPointAddition.InPlace.Semantics.radixUnit p
          fieldTail.succ odd)).execute environment ((AllocatedFixed.placement E (orderWidth
            problem)).frame.register.prod Reference)
            ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
              environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
              Reference)
              (splitChildInput E problem state))).effectWeight
                (SelectedObservation.selectedEffects E problem input
                  ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference))
                    := by
  let caller := (Circuit.embed (allowAllocation := false)
    (AllocatedFixed.placement E (orderWidth problem))
    (Sampling.body E fieldTail (orderWidth problem) seed problem.order points
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))).execute
        environment Reference state
  let child := (Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order
    points (Recovery.Layout.order (orderWidth problem))
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
      ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference)
      ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
        environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
        Reference)
        (splitChildInput E problem state))
  have observation := actual_embedded_terminal_observation_weight (environment := environment)
    (Reference := Reference) (History := History) E fieldTail odd seed problem points state
    (fun stored => selectedExponentEvent problem input
      (publicReadoutBits E (orderWidth problem) stored) = true)
  have callerEffects := congrArg caller.effectWeight (show
      selectedEffects E problem input Reference =
        (fun record => @ite _
          (selectedExponentEvent problem input
            (publicReadoutBits E (orderWidth problem) record.1) = true)
          (Classical.propDecidable _)
          (Effect.one ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
            Reference))
          (Effect.zero ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
            Reference))) from by
    funext record
    dsimp only [selectedEffects]
    by_cases accepted : selectedExponentEvent problem input
      (publicReadoutBits E (orderWidth problem) record.1) = true
    · simp only [if_pos accepted]
    · simp only [if_neg accepted])
  have childEffects := congrArg child.effectWeight (show
      (fun record => @ite _
        (selectedExponentEvent problem input
          (publicReadoutBits E (orderWidth problem)
            ((AllocatedFixed.placement E (orderWidth problem)).store.symm
              (record.1, record.2.2.1.1.1))) = true)
        (Classical.propDecidable _)
        (Effect.one ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
          ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference)))
        (Effect.zero ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
          ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference)))) =
        SelectedObservation.selectedEffects E problem input
          ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference) from by
    funext record
    dsimp only [SelectedObservation.selectedEffects]
    rw [joined_publicReadoutBits]
    by_cases accepted : selectedExponentEvent problem input
      (SelectedObservation.readoutBits p (orderWidth problem) record.1) = true
    · simp only [if_pos accepted]
    · simp only [if_neg accepted])
  exact callerEffects.trans (observation.trans childEffects)

/-- The actual reused public body has the same one-round floor on arbitrary incoming state. -/
lemma actual_embedded_sampling_selected_readout_bound
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (input : SecretInput problem) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((Circuit.embed (allowAllocation := false) (AllocatedFixed.placement E (orderWidth problem))
        (Sampling.body E fieldTail (orderWidth problem) seed problem.order points
          (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))).execute
            environment Reference state).effectWeight
            (selectedEffects E problem input Reference) := by
  have bound := SelectedObservation.actual_reset_converted_selected_readout_bound (environment :=
    environment) E fieldTail odd
    seed problem points sameWidth fits (splitChildInput E problem state) addends input
  rw [splitChildInput_mass] at bound
  exact bound.trans_eq (actual_embedded_selected_readout_weight E fieldTail odd seed problem points
    state input).symm

set_option maxHeartbeats 400000 in
-- The complete allocating observation needs a finite local elaboration budget.
/-- Every complete public terminal Store observation pulls back through actual allocation/embed.
-/
lemma actual_public_terminal_observation_weight
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (event : Store (Recovery.PublicInput.context E (orderWidth problem)) → Prop) :
    ((Sampling.circuit E fieldTail (orderWidth problem) seed problem.order points
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
        Reference
        state).effectWeight
        (fun record => if event record.1 then
          Effect.one ((Recovery.PublicInput.context E (orderWidth problem)).register.prod Reference)
        else Effect.zero ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
          Reference)) =
      ((Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order points
        (Recovery.Layout.order (orderWidth problem))
          (GenericPointAddition.InPlace.Semantics.radixUnit p
          fieldTail.succ odd)).execute environment ((AllocatedFixed.placement E (orderWidth
            problem)).frame.register.prod Reference)
            ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
              environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
              Reference)
              (allocatedChildInput (environment := environment) E problem state))).effectWeight
                (fun record =>
                if event ((AllocatedFixed.placement E (orderWidth problem)).store.symm
                  (record.1, record.2.2.1.1.1)) then
                    Effect.one ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
                      ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
                        Reference))
                else Effect.zero ((Recovery.Layout.terminal p.size (orderWidth
                  problem)).register.prod
                  ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
                    Reference))) :=
    by
  rw [actual_public_sampling_execute (environment := environment)
    (Reference := Reference) (History := History) E fieldTail odd seed problem points state]
  erw [indicator_mapHistory (ctx := Recovery.PublicInput.context E (orderWidth problem))
      (Reference := Reference),
    indicator_join (Reference := Reference) (AllocatedFixed.placement E (orderWidth problem)),
    ExecutionState.effectWeight_mapClassical_decision,
    State.mapHistory, ExecutionState.effectWeight_mapClassical_decision]
  apply congrArg
  funext record
  rfl

set_option maxHeartbeats 800000 in
-- The complete allocating selected event needs a finite local elaboration budget.
/-- Actual allocation and embedding preserve exactly the child's selected-frequency weight. -/
lemma actual_public_selected_readout_weight
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (input : SecretInput problem) :
    ((Sampling.circuit E fieldTail (orderWidth problem) seed problem.order points
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
        Reference
        state).effectWeight
        (selectedEffects E problem input Reference) =
      ((Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order points
        (Recovery.Layout.order (orderWidth problem))
          (GenericPointAddition.InPlace.Semantics.radixUnit p
          fieldTail.succ odd)).execute environment ((AllocatedFixed.placement E (orderWidth
            problem)).frame.register.prod Reference)
            ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
              environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
              Reference)
              (allocatedChildInput (environment := environment) E problem state))).effectWeight
                (SelectedObservation.selectedEffects E problem input
                  ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
                        Reference))
                    :=
    by
  let caller := (Sampling.circuit E fieldTail (orderWidth problem) seed problem.order points
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
      Reference state
  let child := (Recovery.Conversion.convertedStages (m := orderWidth problem) E problem.order
    points (Recovery.Layout.order (orderWidth problem))
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
      ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference)
      ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
        environment ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod
        Reference)
        (allocatedChildInput (environment := environment) E problem state))
  have observation := actual_public_terminal_observation_weight (environment := environment)
    (Reference := Reference) (History := History) E fieldTail odd seed problem points state
    (fun stored => selectedExponentEvent problem input
      (publicReadoutBits E (orderWidth problem) stored) = true)
  have callerEffects := congrArg caller.effectWeight (show
      selectedEffects E problem input Reference =
        (fun record => @ite _
          (selectedExponentEvent problem input
            (publicReadoutBits E (orderWidth problem) record.1) = true)
          (Classical.propDecidable _)
          (Effect.one ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
            Reference))
          (Effect.zero ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
            Reference))) from by
    funext record
    dsimp only [selectedEffects]
    by_cases accepted : selectedExponentEvent problem input
      (publicReadoutBits E (orderWidth problem) record.1) = true
    · simp only [if_pos accepted]
    · simp only [if_neg accepted])
  have childEffects := congrArg child.effectWeight (show
      (fun record => @ite _
        (selectedExponentEvent problem input
          (publicReadoutBits E (orderWidth problem)
            ((AllocatedFixed.placement E (orderWidth problem)).store.symm
              (record.1, record.2.2.1.1.1))) = true)
        (Classical.propDecidable _)
        (Effect.one ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
          ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference)))
        (Effect.zero ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
          ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference)))) =
        SelectedObservation.selectedEffects E problem input
          ((AllocatedFixed.placement E (orderWidth problem)).frame.register.prod Reference) from by
    funext record
    dsimp only [SelectedObservation.selectedEffects]
    rw [joined_publicReadoutBits]
    by_cases accepted : selectedExponentEvent problem input
      (SelectedObservation.readoutBits p (orderWidth problem) record.1) = true
    · simp only [if_pos accepted]
    · simp only [if_neg accepted])
  exact callerEffects.trans (observation.trans childEffects)

/-- The original one-round floor holds for the actual allocating public sampling circuit. -/
lemma actual_public_sampling_selected_readout_bound
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (input : SecretInput problem) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((Sampling.circuit E fieldTail (orderWidth problem) seed problem.order points
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute
          environment Reference
          state).effectWeight
          (selectedEffects E problem input Reference) := by
  have bound := SelectedObservation.actual_reset_converted_selected_readout_bound (environment :=
    environment) E fieldTail odd
    seed problem points sameWidth fits (allocatedChildInput (environment := environment) E problem
      state) addends input
  rw [allocatedChildInput_mass] at bound
  exact bound.trans_eq (actual_public_selected_readout_weight E fieldTail odd seed problem points
    state input).symm

end

end Probability
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
