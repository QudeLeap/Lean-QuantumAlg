/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Embedding.Cells
import all QuantumAlg.Core.Execution.Context.Embedding.Framing
import all QuantumAlg.Core.Execution.Context.Embedding.Permutation
import all QuantumAlg.Core.Execution.Measurement.Cells.State
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Full native state execution with arbitrary resident cell values

The state uses the original recursive cell Store and quantum-reference
coordinates. Native placement retains every complete block and actual path;
no value, history or off-diagonal reference coordinate is discarded.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Native retained-head placement obeys the original complete split-state coordinates. -/
lemma embedRetained_execute {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (code : Circuit model ctx ctx false)
    (environment : model.Environment) {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × H)) :
    underRetainedSplitState key shape fresh
      ((embedRetained code key shape fresh).execute environment Reference state) =
      (code.execute environment
        (Register.prod (retainedLocalFrame (kind := model.kind) key shape).register
        Reference) (underRetainedSplitState key shape fresh state)).mapHistory
          (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  let original := retainedUnionState key shape fresh state
  let framed := Circuit.embed (allowAllocation := false)
    (ContextEmbedding.alongUnion ctx (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh)) code
  let permutation := retainedLocalPermutation ctx key shape fresh
  have permuted := Circuit.permutation_embed_execute (allowAllocation := false)
    permutation framed environment Reference original
  have restored : ContextPermutation.state permutation original = state :=
    retainedUnionState_inverse key shape fresh state
  rw [restored] at permuted
  have actual : retainedUnionState key shape fresh
      ((embedRetained code key shape fresh).execute environment Reference state) =
        framed.execute environment Reference original := by
    change retainedUnionState key shape fresh
      ((Circuit.embed (allowAllocation := false)
        (ContextEmbedding.alongPermutation permutation) framed).execute environment
          Reference state) =
      framed.execute environment Reference original
    rw [permuted]
    exact retainedUnionState_permuted key shape fresh _
  change ContextUnion.splitServiceState ctx (retainedLocalFrame (kind := model.kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh)
    (retainedUnionState key shape fresh
      ((embedRetained code key shape fresh).execute environment Reference state)) = _
  rw [actual]
  exact Circuit.union_embed_execute (allowAllocation := false) code environment
    (retainedLocalFrame key shape) (retainedLocalDisjoint ctx key shape fresh) Reference original

/-- Native cells execute the full original child with all existing Stores and paths retained. -/
lemma embedMeasurementCells_execute {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (dimension : ℕ+) (code : Circuit model ctx ctx false)
    (count : Nat) (environment : model.Environment) {Reference : Register} {H : Type} [Fintype H]
    (state : State (MeasurementCells.context ctx dimension count) Reference
      (model.HiddenState × H)) :
    underMeasurementCellsSplitState ctx dimension count
      ((embedMeasurementCells code dimension count).execute environment Reference state) =
      (code.execute environment (measurementCellsReference ctx dimension count Reference)
        (underMeasurementCellsSplitState ctx dimension count state)).mapHistory
          (fun record => (record.1, (record.2.1.1,
            (record.2.1.2, embedMeasurementCellsPathEquiv code dimension count record.2.2)))) := by
  induction count generalizing Reference H with
  | zero =>
      simp only [underMeasurementCellsSplitState, measurementCellsReference,
        embedMeasurementCells, embedMeasurementCellsPathEquiv]
      erw [execute_mapHistory code environment Reference state (fun history : H => ((), history))]
      erw [State.mapHistory_comp]
      rfl
  | succ count ih =>
      let inner := MeasurementCells.context ctx dimension count
      let prior := embedMeasurementCells code dimension count
      let split := underRetainedSplitState inner.canonicalFreshKey (.finite dimension)
        inner.canonicalFreshKey_fresh state
      simp only [underMeasurementCellsSplitState, measurementCellsReference, embedMeasurementCells]
      erw [embedRetained_execute inner.canonicalFreshKey (.finite dimension)
        inner.canonicalFreshKey_fresh prior environment state]
      erw [underMeasurementCellsSplitState_history ctx dimension count
        (prior.execute environment
          ((measurementCellFrame ctx dimension count).register.prod Reference) split)
        (fun record : (Store (measurementCellFrame ctx dimension count) × H) × prior.Path =>
          (record.1.1, (record.1.2, record.2)))]
      erw [ih (state := split)]
      erw [execute_mapHistory code environment
        (measurementCellsReference ctx dimension count
          ((measurementCellFrame ctx dimension count).register.prod Reference))
        (underMeasurementCellsSplitState ctx dimension count split)
        (fun record : measurementCellsHistory ctx dimension count ×
          (Store (measurementCellFrame ctx dimension count) × H) =>
          ((record.1, record.2.1), record.2.2))]
      repeat' erw [State.mapHistory_comp]
      rfl

end

end QuantumAlg.Circuit
