/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Reset
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Layout

/-!
# Guarded quadratic recovery

One recovered short logarithm is optional.  This routine resets only the
reusable square-root words, runs the quadratic factor checker when that option
is present, and otherwise preserves the persistent factor selector.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticRecoveryGuarded

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The short-log selector and the quadratic factor-recovery package. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Nested references for the short log selection stage. -/
  shortLogSelection : FirstAccepted.Direct.Refs ctx shortWidth
  /-- Nested references for the quadratic stage. -/
  quadratic : QuadraticRecoveryReset.Refs ctx shortWidth
  shortLogInput :
    quadratic.recovery.candidates.quadraticPrefix.shortLog =
      FirstAccepted.cellRead shortLogSelection.selected

/-- The persistent selector holding the first recovered factor. -/
abbrev factorSelection {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) :=
  refs.quadratic.recovery.pair.first.selection

/-- Decode the optional short logarithm supplied by the preceding pair scan. -/
def sourceOption {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : FirstAccepted.Direct.Refs ctx width)
    (observation : Store ctx) : Option Nat :=
  if (observation.read (FirstAccepted.cellRead refs.accepted)).toBool then
    some (observation.read (FirstAccepted.cellRead refs.selected)).toNat
  else
    none

/-- Convert an optional short logarithm into its optional quadratic factor. -/
def recoveryOption (modulus : Nat) : Option Nat → Option Nat
  | none => none
  | some shortLog => RSA.recoverFactorFromShortLog modulus shortLog

/-- Persistent constants required after the reusable scratch reset. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (modulus : Nat) (before : Store ctx)
    (refs : Refs ctx shortWidth) : Prop where
  pair : QuadraticCandidatePairSelect.InitialConditions before
    refs.quadratic.recovery.pair
  modulusValue :
    (before.read refs.quadratic.recovery.candidates.quadraticPrefix.modulus).toNat = modulus

/-- Local separation and every persistent read framed by the scratch reset. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) : Prop where
  reset : QuadraticRecoveryReset.Separation refs.quadratic
  recovery : QuadraticRecoveryMachine.Separation refs.quadratic.recovery
  sourceAcceptedReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    (FirstAccepted.cellRead refs.shortLogSelection.accepted)
  sourceSelectedReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    (FirstAccepted.cellRead refs.shortLogSelection.selected)
  modulusReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.candidates.quadraticPrefix.modulus
  firstOneReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.pair.first.check.one
  firstModulusReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.pair.first.check.positiveCheck.modulus
  firstZeroReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.pair.first.check.positiveCheck.zero
  secondOneReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.pair.second.check.one
  secondModulusReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.pair.second.check.positiveCheck.modulus
  secondZeroReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    refs.quadratic.recovery.pair.second.check.positiveCheck.zero
  factorAcceptedReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    (FirstAccepted.cellRead (factorSelection refs).accepted)
  factorSelectedReset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic
    (FirstAccepted.cellRead (factorSelection refs).selected)

/-- One caller read avoids the reset and the optional quadratic recovery. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  reset : QuadraticRecoveryReset.CallerFrameAvoids refs.quadratic other
  recovery : QuadraticRecoveryMachine.CallerFrameAvoids
    refs.quadratic.recovery other

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Select the actual recovery circuit exactly when the short-log latch is set. -/
def arm (refs : Refs ctx shortWidth) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => .id ctx
  | .bit true => QuadraticRecoveryMachine.into refs.quadratic.recovery

/-- Complete actual store and selected-arm path. -/
def armStep (refs : Refs ctx shortWidth) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (arm refs flag).Path :=
  match flag with
  | .bit false => (store, ())
  | .bit true => QuadraticRecoveryMachine.step refs.quadratic.recovery store

/-- Dispatch through the existing classical short-log acceptance cell. -/
def chooseInto (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .branch (FirstAccepted.cellRead refs.shortLogSelection.accepted) (arm refs)

/-- Record exactly the value read from the real acceptance cell and its actual arm. -/
def chooseStep (refs : Refs ctx shortWidth) (store : Store ctx) :
    Store ctx × (chooseInto refs).Path :=
  let flag := store.read (FirstAccepted.cellRead refs.shortLogSelection.accepted)
  let chosen := armStep refs flag store
  (chosen.1, ⟨flag, chosen.2⟩)

/-- Charge the four scratch clears, then dispatch on the existing short-log option. -/
def into (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (QuadraticRecoveryReset.into refs.quadratic) (chooseInto refs)

/-- The reset and selected body return one actual store and one chronological circuit path. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  Circuit.sequenceStoreRecord (QuadraticRecoveryReset.into refs.quadratic) (chooseInto refs)
    (QuadraticRecoveryReset.step refs.quadratic) (chooseStep refs) store

/-- The selected store follows the actual true-recovery or false-identity arm. -/
lemma chooseStep_store (refs : Refs ctx shortWidth) (store : Store ctx) :
    (chooseStep refs store).1 =
      if (store.read (FirstAccepted.cellRead refs.shortLogSelection.accepted)).toBool then
        (QuadraticRecoveryMachine.step refs.quadratic.recovery store).1 else store := by
  unfold chooseStep
  cases value : store.read (FirstAccepted.cellRead refs.shortLogSelection.accepted) with
  | bit flag => cases flag <;> rfl

private lemma arm_execute (refs : Refs ctx shortWidth) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (arm refs flag).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := armStep refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
      cases flag with
      | false =>
          refine (Circuit.execute_id_mapClassical
            (environment := environment) Reference state).trans ?_
          exact ExecutionState.executionState_mapClassical_congr _ rfl
      | true => exact QuadraticRecoveryMachine.into_execute refs.quadratic.recovery Reference state

/-- Actual stored-value dispatch preserves complete history and external-reference blocks. -/
lemma chooseInto_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (chooseInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := chooseStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (environment := environment)
    (FirstAccepted.cellRead refs.shortLogSelection.accepted) (arm refs)
    (fun flag before =>
      let actual := armStep refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => arm_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete reset-and-branch execution follows its actual full-store record. -/
lemma into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord
    (environment := environment) (QuadraticRecoveryReset.into refs.quadratic)
    (chooseInto refs) (QuadraticRecoveryReset.step refs.quadratic) (chooseStep refs)
    (QuadraticRecoveryReset.into_execute refs.quadratic) (chooseInto_execute refs)
    Reference state

/-- Caller reads outside the reset and optional recovery writes survive either actual branch. -/
lemma into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other := by
  change (chooseStep refs (QuadraticRecoveryReset.step refs.quadratic store).1).1.read other = _
  rw [chooseStep_store]
  split
  · exact (QuadraticRecoveryMachine.into_callerFrame refs.quadratic.recovery _
      other avoids.recovery).trans
      (QuadraticRecoveryReset.into_callerFrame refs.quadratic store other avoids.reset)
  · exact QuadraticRecoveryReset.into_callerFrame refs.quadratic store other avoids.reset

/-- Optional recovery retains an earlier factor and preserves the complete caller frame. -/
structure Relation (modulus : Nat) (refs : Refs ctx shortWidth)
    (before after : Store ctx) : Prop where
  selected : QuadraticCandidateSelect.selectedOption (factorSelection refs) after =
    FirstAccepted.retainFirst
      (QuadraticCandidateSelect.selectedOption (factorSelection refs) before)
      (recoveryOption modulus (sourceOption refs.shortLogSelection before))
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- The actual reset-and-branch circuit realizes the original optional quadratic recovery. -/
lemma into_correct (modulus : Nat) (refs : Refs ctx shortWidth)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions modulus store refs) :
    Relation modulus refs store (step refs store).1 := by
  let middle := (QuadraticRecoveryReset.step refs.quadratic store).1
  have sourceAccepted := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.sourceAcceptedReset
  have sourceSelected := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.sourceSelectedReset
  have sourceAtReset : sourceOption refs.shortLogSelection middle =
      sourceOption refs.shortLogSelection store := by
    unfold sourceOption
    rw [sourceAccepted, sourceSelected]
  have factorAccepted := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.factorAcceptedReset
  have factorSelected := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.factorSelectedReset
  have factorAtReset : QuadraticCandidateSelect.selectedOption (factorSelection refs) middle =
      QuadraticCandidateSelect.selectedOption (factorSelection refs) store := by
    unfold QuadraticCandidateSelect.selectedOption FirstAccepted.selectedOption
    rw [factorAccepted, factorSelected]
  have one₁ := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.firstOneReset
  have modulus₁ := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.firstModulusReset
  have zero₁ := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.firstZeroReset
  have one₂ := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.secondOneReset
  have modulus₂ := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.secondModulusReset
  have zero₂ := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.secondZeroReset
  have pairInitial : QuadraticRecoveryMachine.InitialConditions middle refs.quadratic.recovery := by
    unfold QuadraticRecoveryMachine.InitialConditions QuadraticCandidatePairSelect.InitialConditions
      QuadraticCandidateCheck.TotalInitialConditions
    rw [one₁, modulus₁, zero₁, one₂, modulus₂, zero₂]
    exact initial.pair
  have modulusFrame := QuadraticRecoveryReset.into_callerFrame refs.quadratic store
    _ separation.modulusReset
  have modulusAtReset :
      (middle.read refs.quadratic.recovery.candidates.quadraticPrefix.modulus).toNat = modulus :=
    (congrArg CShape.Value.toNat modulusFrame).trans initial.modulusValue
  refine ⟨?_, into_callerFrame refs store⟩
  change QuadraticCandidateSelect.selectedOption (factorSelection refs)
    (chooseStep refs middle).1 = _
  rw [chooseStep_store]
  by_cases accepted : (middle.read (FirstAccepted.cellRead refs.shortLogSelection.accepted)).toBool
      = true
  · rw [if_pos accepted]
    let shortLog := (middle.read refs.quadratic.recovery.candidates.quadraticPrefix.shortLog).toNat
    have sourceSome : sourceOption refs.shortLogSelection store = some shortLog := by
      rw [← sourceAtReset]
      unfold sourceOption
      rw [if_pos accepted, ← refs.shortLogInput]
    have recovered := QuadraticRecoveryMachine.into_correct refs.quadratic.recovery
      separation.recovery middle pairInitial
    have retained := QuadraticRecoveryMachine.relation_retains_recoverFactorFromShortLog
      refs.quadratic.recovery middle _ recovered shortLog rfl modulus modulusAtReset
    simpa only [factorSelection, factorAtReset, sourceSome, recoveryOption] using retained
  · rw [if_neg accepted]
    have sourceNone : sourceOption refs.shortLogSelection store = none := by
      rw [← sourceAtReset]
      unfold sourceOption
      rw [if_neg accepted]
    rw [sourceNone, recoveryOption, factorAtReset]
    cases QuadraticCandidateSelect.selectedOption (factorSelection refs) store <;> rfl

/-- Independent allowance for four actual clears and the maximum optional recovery branch. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool model :=
  QuadraticRecoveryReset.resetEventEnvelope shortWidth +
    ResourcePool.max (QuadraticRecoveryMachine.eventEnvelope shortWidth) 0

/-- The same recorded path charges every reset instruction and only the selected recovery arm. -/
lemma into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path =
      (QuadraticRecoveryReset.into refs.quadratic).eventTrace path.1 ++
        (arm refs path.2.1).eventTrace path.2.2 := rfl

/-- All actual native coordinates meet the independent reset-and-maximum-branch allowance. -/
lemma into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  change ResourcePool.ofList ((QuadraticRecoveryReset.into refs.quadratic).eventTrace path.1 ++
    (arm refs path.2.1).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  apply add_le_add (QuadraticRecoveryReset.into_pool_le refs.quadratic path.1)
  rcases path.2 with ⟨flag, selected⟩
  cases flag with
  | bit flag =>
      cases flag with
      | false => exact ResourcePool.le_max_right _ _
      | true => exact (QuadraticRecoveryMachine.into_pool_le
          refs.quadratic.recovery selected).trans (ResourcePool.le_max_left _ _)

/-- Depth charges all four reset instructions before the optional complete recovery. -/
lemma into_depth_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path ≤
      7 * QuadraticPrefix.discriminantWidth shortWidth + 38 := by
  change (QuadraticRecoveryReset.into refs.quadratic).depth (fun _ => 1) path.1 +
    (arm refs path.2.1).depth (fun _ => 1) path.2.2 ≤ _
  rw [QuadraticRecoveryReset.into_depth]
  rcases path.2 with ⟨flag, selected⟩
  cases flag with
  | bit flag =>
      cases flag with
      | false => change 4 + 0 ≤ _; omega
      | true =>
          have bound := QuadraticRecoveryMachine.into_depth_le refs.quadratic.recovery selected
          change 4 + (QuadraticRecoveryMachine.into refs.quadratic.recovery).depth
            (fun _ => 1) selected ≤ _
          omega

/-- Every branch keeps all supplied classical and quantum runtime entries live. -/
lemma into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨resetPath, flag, selected⟩
  change visited ∈ (QuadraticRecoveryReset.into refs.quadratic).visitedContexts resetPath ++
    (arm refs flag).visitedContexts selected at present
  rcases List.mem_append.mp present with reset | chosen
  · rw [QuadraticRecoveryReset.into_visited] at reset
    exact (List.mem_replicate.mp reset).2
  · cases flag with
    | bit flag =>
        cases flag with
        | false => exact List.mem_singleton.mp chosen
        | true =>
            exact QuadraticRecoveryMachine.into_visited
              refs.quadratic.recovery selected visited chosen

/-- Resident space includes every caller and reusable scratch cell in either selected branch. -/
lemma into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary space preserves all workspace roles through reset and optional recovery. -/
lemma into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Both actual branches restore borrowed systems jointly with every external quantum reference. -/
lemma into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored
      Reference state ((into refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact QuadraticRecoveryReset.into_borrowedRestored refs.quadratic Reference state
  · apply Circuit.borrowedRestored_branch (environment := environment)
    intro flag History _ selected
    cases flag with
    | bit flag =>
        cases flag with
        | false =>
            exact Circuit.borrowedRestored_id (environment := environment) (model := model) selected
        | true =>
            exact QuadraticRecoveryMachine.into_borrowedRestored
              refs.quadratic.recovery Reference selected

end

end QuadraticRecoveryGuarded
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
