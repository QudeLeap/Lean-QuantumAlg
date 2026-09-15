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

variable {kind : ProblemKind}

/-- The actual recursive allocation records agree at every retained-cell instruction. -/
def allocateFramedPathEquiv (ctx frame : RuntimeCtx kind) (dimension : ℕ+) :
    (count : Nat) → (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame) →
      (allocate ctx dimension count).Path ≃ (allocateFramed ctx frame dimension count separate).Path
  | 0, _ => Equiv.refl _
  | count + 1, separate =>
      (allocateFramedPathEquiv ctx frame dimension count
        (retained_disjoint (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh separate)).prodCongr
            (Equiv.refl Unit)

private theorem retain_splitState {ctx frame : RuntimeCtx kind}
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

/-- Actual retained allocation preserves every complete frame block and its physical reference. -/
theorem allocateFramed_execute (ctx frame : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate))
      Reference History) :
    splitState (context ctx dimension count) frame separate
      ((allocateFramed ctx frame dimension count separate).execute Reference state) =
      ((allocate ctx dimension count).execute (Register.prod frame.register Reference)
        (splitState ctx frame (original_disjoint ctx frame dimension count separate)
          state)).mapHistory
            (fun record => (record.1.1,
              (record.1.2,
                allocateFramedPathEquiv ctx frame dimension count separate record.2))) := by
  induction count with
  | zero =>
      exact contextUnion_splitState_skip ctx frame separate state
  | succ count ih =>
      let middle := context ctx dimension count
      let prefixSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      let framedPrefix := allocateFramed ctx frame dimension count prefixSeparate
      let fresh := retained_fresh_union middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      change splitState (middle.addRetained middle.canonicalFreshKey (.finite dimension)
          middle.canonicalFreshKey_fresh) frame separate
        (((framedPrefix.execute Reference state).retain middle.canonicalFreshKey
          (.finite dimension) fresh).mapHistory
            (fun record => (record.1.1, (record.1.2, record.2)))) = _
      erw [contextUnion_splitState_mapHistory, retain_splitState,
        ih prefixSeparate state, State.mapHistory_retain]
      change _ = ((Circuit.seq (allocate ctx dimension count)
        (.retain middle middle.canonicalFreshKey (.finite dimension)
          middle.canonicalFreshKey_fresh)).execute (Register.prod frame.register Reference)
          (splitState ctx frame
            (original_disjoint ctx frame dimension count prefixSeparate) state)).mapHistory _
      rw [Circuit.execute_seq, Circuit.execute_retain]
      simp only [State.mapHistory_comp, Function.comp_def, allocateFramedPathEquiv]
      erw [State.mapHistory_comp]
      rfl

end

end QuantumAlg.Execution.MeasurementCells
