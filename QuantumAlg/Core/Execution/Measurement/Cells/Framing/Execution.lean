/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Framing
import all QuantumAlg.Core.Execution.Context.Union.State.Laws
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Complete execution naturality of framed measurement-cell allocation

Every original retained cell is initialized by the existing interpreter.
Exact store and quantum coordinates keep the entire resident frame, external
reference and actual recursive allocation path. No independence assumption
or restriction to a classical frame is imposed.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

open ContextUnion

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} (environment : model.Environment)

/-- The actual recursive allocation records agree at every retained-cell instruction. -/
def allocateFramedPathEquiv (ctx frame : RuntimeCtx model.kind) (dimension : ℕ+) :
    (count : Nat) → (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame) →
      (allocate (model := model) ctx dimension count).Path ≃
        (allocateFramed (model := model) ctx frame dimension count separate).Path
  | 0, _ => Equiv.refl _
  | count + 1, separate =>
      (allocateFramedPathEquiv ctx frame dimension count
        (retained_disjoint (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh separate)).prodCongr
            (Equiv.refl Unit)

private lemma retain_splitState {ctx frame : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (separate : RuntimeCtx.StorageDisjoint (ctx.addRetained key shape fresh) frame)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion frame (retained_disjoint key shape fresh separate))
      Reference History) :
    splitState (ctx.addRetained key shape fresh) frame separate
      (state.retain key shape (retained_fresh_union key shape fresh separate)) =
      ((splitState ctx frame (retained_disjoint key shape fresh separate) state).retain
        key shape fresh).mapHistory (fun record => (record.1.1, (record.1.2, record.2))) := by
  let priorSeparate := retained_disjoint key shape fresh separate
  let actualFresh := retained_fresh_union key shape fresh separate
  let basis := referenceBasis ctx frame priorSeparate Reference
  let inputs := recordEquiv ctx frame priorSeparate History
  let outputs := recordEquiv (ctx.addRetained key shape fresh) frame separate (History × Unit)
  let original := fun record : Store (ctx.disjointUnion frame priorSeparate) × History =>
    (record.1.pushRetained key shape actualFresh, (record.2, ()))
  let framed := fun record : Store ctx × (Store frame × History) =>
    (record.1.pushRetained key shape fresh, (record.2.1, (record.2.2, ())))
  have diagram : ∀ record, outputs (original record) = framed (inputs record) := by
    intro record
    rfl
  have transported := ExecutionState.coordinate_transport_diagram state basis inputs outputs
    original framed diagram
  have target : ((splitState ctx frame priorSeparate state).retain key shape fresh).mapHistory
      (fun record => (record.1.1, (record.1.2, record.2))) =
        ((state.mapClassical inputs).reindex basis).mapClassical framed := by
    simp only [State.retain, State.mapHistory,
      ExecutionState.executionState_mapClassical_comp, Function.comp_def]
    congr 1
    exact Subsingleton.elim _ _
  have source : splitState (ctx.addRetained key shape fresh) frame separate
      (state.retain key shape actualFresh) =
        ((state.mapClassical original).mapClassical outputs).reindex basis := by
    have sameBasis : referenceBasis (ctx.addRetained key shape fresh) frame separate Reference =
        basis := by rfl
    have retained : state.retain key shape actualFresh = state.mapClassical original :=
      State.mapClassical_decision _ _ _ _
    dsimp only [splitState, outputs]
    erw [sameBasis, retained]
    congr 1
    exact State.mapClassical_decision _ _ _ _
  exact source.trans (transported.trans target.symm)

private lemma id_as_history {ctx : RuntimeCtx model.kind} {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.id (allowAllocation := true) (model := model) ctx).execute
          environment Reference state =
      state.skip.mapHistory
        (fun record => (record.1.1, (record.1.2, record.2))) := by
  rw [Circuit.execute_id]
  simp only [State.skip, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private lemma retain_as_history {ctx : RuntimeCtx model.kind} {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference (model.HiddenState × H))
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (Circuit.retain (model := model) ctx key shape fresh).execute environment Reference state =
      (state.retain key shape fresh).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2))) := by
  rw [Circuit.execute_retain]
  simp only [State.retain, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private lemma retain_splitServiceState {ctx frame : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (separate : RuntimeCtx.StorageDisjoint (ctx.addRetained key shape fresh) frame)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.disjointUnion frame (retained_disjoint key shape fresh separate))
      Reference (model.HiddenState × H)) :
    splitServiceState (ctx.addRetained key shape fresh) frame separate
      ((Circuit.retain (model := model)
        (ctx.disjointUnion frame (retained_disjoint key shape fresh separate))
        key shape (retained_fresh_union key shape fresh separate)).execute
          environment Reference state) =
      ((splitServiceState ctx frame (retained_disjoint key shape fresh separate)
        state).retain key shape fresh).mapHistory
          (fun record => (record.1.1, (record.1.2.1, (record.1.2.2, record.2)))) := by
  rw [retain_as_history]
  dsimp only [Circuit.Path]
  unfold splitServiceState
  erw [contextUnion_splitState_mapHistory, retain_splitState]
  erw [State.mapHistory_retain]
  simp only [State.mapHistory_comp, Function.comp_def]
  rfl

/-- Actual retained allocation preserves every complete frame block and its physical reference. -/
lemma allocateFramed_execute (ctx frame : RuntimeCtx model.kind) (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate))
      Reference (model.HiddenState × History)) :
    splitServiceState (context ctx dimension count) frame separate
      ((allocateFramed (model := model) ctx frame dimension count separate).execute
        environment Reference state) =
      ((allocate (model := model) ctx dimension count).execute
        environment (Register.prod frame.register Reference)
        (splitServiceState ctx frame (original_disjoint ctx frame dimension count separate)
          state)).mapHistory
            (fun record => (record.1,
              (record.2.1.1, (record.2.1.2,
                allocateFramedPathEquiv ctx frame dimension count separate record.2.2)))) := by
  induction count with
  | zero =>
      change splitServiceState ctx frame separate
        ((Circuit.id (allowAllocation := true) (model := model)
          (ctx.disjointUnion frame separate)).execute
          environment Reference state) =
        ((Circuit.id (allowAllocation := true) (model := model) ctx).execute
          environment (Register.prod frame.register Reference)
          (splitServiceState ctx frame separate state)).mapHistory _
      rw [id_as_history, id_as_history]
      unfold splitServiceState
      erw [contextUnion_splitState_mapHistory, contextUnion_splitState_skip]
      simp only [State.skip, State.mapHistory_comp, Function.comp_def]
      simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def]
      congr 1
  | succ count ih =>
      let middle := context ctx dimension count
      let prefixSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      let framedPrefix := allocateFramed (model := model) ctx frame dimension count prefixSeparate
      let fresh := retained_fresh_union middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      change splitServiceState (middle.addRetained middle.canonicalFreshKey
        (.finite dimension) middle.canonicalFreshKey_fresh) frame separate
        (((Circuit.retain (middle.disjointUnion frame prefixSeparate)
          middle.canonicalFreshKey (.finite dimension) fresh).execute environment Reference
            (framedPrefix.execute environment Reference state)).mapHistory
              (fun history => (history.1, (history.2.1.1,
                (history.2.1.2, history.2.2))))) = _
      have splitMapped := contextUnion_splitServiceState_mapHistory
        (middle.addRetained middle.canonicalFreshKey (.finite dimension)
          middle.canonicalFreshKey_fresh) frame separate
        ((Circuit.retain (middle.disjointUnion frame prefixSeparate)
          middle.canonicalFreshKey (.finite dimension) fresh).execute environment Reference
            (framedPrefix.execute environment Reference state))
        (fun history => (history.1.1, (history.1.2, history.2)))
      erw [splitMapped]
      rw [retain_splitServiceState, ih prefixSeparate state, State.mapHistory_retain]
      change _ = ((Circuit.seq (allocate (model := model) ctx dimension count)
        (.retain middle middle.canonicalFreshKey (.finite dimension)
          middle.canonicalFreshKey_fresh)).execute
          environment (Register.prod frame.register Reference)
          (splitServiceState ctx frame
            (original_disjoint ctx frame dimension count prefixSeparate) state)).mapHistory _
      rw [Circuit.execute_seq, retain_as_history]
      simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def]
      congr 1

end

end QuantumAlg.Execution.MeasurementCells
