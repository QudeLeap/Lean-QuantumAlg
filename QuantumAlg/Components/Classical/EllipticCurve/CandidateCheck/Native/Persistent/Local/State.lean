/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Path
import all QuantumAlg.Core.Execution.Local.Cells.State

/-!
# Complete state beside the seven existing recovery cells

Only exact Store and reference coordinates are composed here. The executable
circuit is the existing seven-cell extension, in its original order. Every
stored value and quantum correlation is retained, without initialization or
support assumptions and without another execution rule.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private structure RetainedCoordinates (base outer : RuntimeCtx kind) where
  History : Type
  [finiteHistory : Fintype History]
  reference : Register → Register
  splitState : {Reference : Register} → {H : Type} → [Fintype H] →
    State outer Reference H → State base (reference Reference) (History × H)
  split_history : ∀ {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State outer Reference H) (update : H → K),
    splitState (state.mapHistory update) =
      (splitState state).mapHistory (fun record => (record.1, update record.2))

attribute [instance] RetainedCoordinates.finiteHistory

private def originalCoordinates (base : RuntimeCtx kind) : RetainedCoordinates base base where
  History := Unit
  reference := id
  splitState state := state.mapHistory (fun history => ((), history))
  split_history state update := by
    simp only [State.mapHistory_comp, Function.comp_def]

private def retainCoordinates {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer) (shape : CShape) :
    RetainedCoordinates base
      (outer.addRetained outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh) where
  History := prior.History × Store (Circuit.retainedLocalFrame (kind := kind)
    outer.canonicalFreshKey shape)
  reference reference := prior.reference
    ((Circuit.retainedLocalFrame (kind := kind) outer.canonicalFreshKey shape).register.prod
      reference)
  splitState state :=
    (prior.splitState (Circuit.underRetainedSplitState outer.canonicalFreshKey shape
      outer.canonicalFreshKey_fresh state)).mapHistory
        (fun record => ((record.1, record.2.1), record.2.2))
  split_history state update := by
    rw [Circuit.retainedSplit_history, prior.split_history]
    simp only [State.mapHistory_comp, Function.comp_def]

private def RetainedCoordinates.executedState {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (code : Circuit base base) (extended : Circuit outer outer)
    (path : code.Path ≃ extended.Path) {Reference : Register} {H : Type} [Fintype H]
    (state : State outer Reference H) :
    State base (coordinates.reference Reference) (coordinates.History × (H × extended.Path)) :=
  (code.execute (coordinates.reference Reference) (coordinates.splitState state)).mapHistory
    (fun record => (record.1.1, (record.1.2, path record.2)))

private def RetainedCoordinates.Executes {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (code : Circuit base base) (extended : Circuit outer outer)
    (path : code.Path ≃ extended.Path) : Prop :=
  ∀ {Reference : Register} {H : Type} [Fintype H] (state : State outer Reference H),
    coordinates.splitState (extended.execute Reference state) =
      (code.execute (coordinates.reference Reference) (coordinates.splitState state)).mapHistory
        (fun record => (record.1.1, (record.1.2, path record.2)))

private theorem originalCoordinates_execute (code : Circuit ctx ctx) :
    (originalCoordinates ctx).Executes code code (Equiv.refl _) := by
  intro Reference H _ state
  change (code.execute Reference state).mapHistory (fun history => ((), history)) =
    (code.execute Reference (state.mapHistory (fun history => ((), history)))).mapHistory
      (fun record => (record.1.1, (record.1.2, record.2)))
  rw [Circuit.execute_mapHistory, State.mapHistory_comp]
  rfl

private theorem retainCoordinates_execute {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer) (code : Circuit base base)
    (localCode : { code : Circuit outer outer // code.IsLocal })
    (path : code.Path ≃ localCode.val.Path) (natural : prior.Executes code localCode.val path)
    (shape : CShape) :
    (retainCoordinates prior shape).Executes code (besideCell localCode shape).val
      (besidePath localCode shape path) := by
  intro Reference H _ state
  change (prior.splitState
    (Circuit.underRetainedSplitState outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh
      ((Circuit.underRetained localCode.val localCode.property outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh).execute Reference state))).mapHistory
          (fun record => ((record.1, record.2.1), record.2.2)) =
    (code.execute
      (prior.reference ((Circuit.retainedLocalFrame (kind := kind)
        outer.canonicalFreshKey shape).register.prod Reference))
      ((prior.splitState (Circuit.underRetainedSplitState outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh state)).mapHistory
          (fun record => ((record.1, record.2.1), record.2.2)))).mapHistory
            (fun record => (record.1.1, (record.1.2, besidePath localCode shape path record.2)))
  erw [Circuit.underRetained_execute, prior.split_history, natural, Circuit.execute_mapHistory]
  erw [State.mapHistory_comp, State.mapHistory_comp, State.mapHistory_comp]
  rfl

private def persistentCoordinates (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    RetainedCoordinates ctx (persistentCtx ctx width scalarWidth) :=
  let accepted := retainCoordinates (originalCoordinates ctx) .bit
  let selected := retainCoordinates accepted (.unsignedWord scalarWidth)
  let inverse := retainCoordinates selected .bit
  let candidate := retainCoordinates inverse (.unsignedWord scalarWidth)
  let reconstruction := retainCoordinates candidate .bit
  let verified := retainCoordinates reconstruction .bit
  retainCoordinates verified (PointShape width)

/-- The complete actual Stores of all seven persistent cells, in their original allocation order. -/
def persistentLocalHistory (ctx : RuntimeCtx kind) (width scalarWidth : Nat) : Type :=
  (persistentCoordinates ctx width scalarWidth).History

/-- The actual persistent cells form a finite retained history. -/
noncomputable instance persistentLocalHistoryFintype
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    Fintype (persistentLocalHistory ctx width scalarWidth) :=
  (persistentCoordinates ctx width scalarWidth).finiteHistory

/-- Keep the complete reference with the exact zero-wire registers of the existing cells. -/
def persistentLocalReference (ctx : RuntimeCtx kind) (width scalarWidth : Nat)
    (reference : Register) : Register :=
  (persistentCoordinates ctx width scalarWidth).reference reference

/-- Split all seven existing cells without changing their values or discarding correlations. -/
def underPersistentSplitState (width scalarWidth : Nat) {Reference : Register}
    {H : Type} [Fintype H] (state : State (persistentCtx ctx width scalarWidth) Reference H) :
    State ctx (persistentLocalReference ctx width scalarWidth Reference)
      (persistentLocalHistory ctx width scalarWidth × H) :=
  (persistentCoordinates ctx width scalarWidth).splitState state

/-- The seven real cell Stores are preserved through every original history-coordinate map. -/
theorem underPersistentSplitState_history (width scalarWidth : Nat) {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) (update : H → K) :
    underPersistentSplitState width scalarWidth (state.mapHistory update) =
      (underPersistentSplitState width scalarWidth state).mapHistory
        (fun record => (record.1, update record.2)) :=
  (persistentCoordinates ctx width scalarWidth).split_history state update

private theorem firstThreeCoordinates_execute
    (code : Circuit ctx ctx) (supported : code.IsLocal) (scalarWidth : Nat) :
    (retainCoordinates
      (retainCoordinates (retainCoordinates (originalCoordinates ctx) .bit)
        (.unsignedWord scalarWidth)) .bit).Executes code
      (besideCell (besideCell (besideCell ⟨code, supported⟩ .bit)
        (.unsignedWord scalarWidth)) .bit).val
      (besidePath (besideCell (besideCell ⟨code, supported⟩ .bit)
        (.unsignedWord scalarWidth)) .bit
        (besidePath (besideCell ⟨code, supported⟩ .bit) (.unsignedWord scalarWidth)
          (besidePath ⟨code, supported⟩ .bit (Equiv.refl _)))) := by
  let original := (⟨code, supported⟩ : { code : Circuit ctx ctx // code.IsLocal })
  have accepted := @retainCoordinates_execute _ _ _ (originalCoordinates ctx) code original
    (Equiv.refl _) (originalCoordinates_execute code) .bit
  have selected := @retainCoordinates_execute _ _ _ _ code (besideCell original .bit) _ accepted
    (.unsignedWord scalarWidth)
  have inverse := @retainCoordinates_execute _ _ _ _ code
    (besideCell (besideCell original .bit) (.unsignedWord scalarWidth)) _ selected .bit
  exact @inverse

private theorem persistentCoordinates_execute
    (code : Circuit ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat) :
    (persistentCoordinates ctx width scalarWidth).Executes code
      (underPersistent code supported width scalarWidth)
      (underPersistentPathEquiv code supported width scalarWidth) := by
  have inverse := @firstThreeCoordinates_execute _ _ code supported scalarWidth
  have candidate := @retainCoordinates_execute _ _ _ _ code _ _ inverse (.unsignedWord scalarWidth)
  have reconstruction := @retainCoordinates_execute _ _ _ _ code _ _ candidate .bit
  have verified := @retainCoordinates_execute _ _ _ _ code _ _ reconstruction .bit
  have scalar := @retainCoordinates_execute _ _ _ _ code _ _ verified (PointShape width)
  exact @scalar

/-- Execute the original code in the complete split coordinates and retain its actual path. -/
def underPersistentExecutionState (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) :
    State ctx (persistentLocalReference ctx width scalarWidth Reference)
      (persistentLocalHistory ctx width scalarWidth ×
        (H × (underPersistent code supported width scalarWidth).Path)) :=
  (persistentCoordinates ctx width scalarWidth).executedState code
    (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth) state

/-- The complete actual state follows the original local circuit and its exact path equivalence. -/
theorem underPersistent_execute (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) :
    underPersistentSplitState width scalarWidth
        ((underPersistent code supported width scalarWidth).execute Reference state) =
      underPersistentExecutionState code supported width scalarWidth state :=
  @persistentCoordinates_execute kind ctx code supported width scalarWidth Reference H _ state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
