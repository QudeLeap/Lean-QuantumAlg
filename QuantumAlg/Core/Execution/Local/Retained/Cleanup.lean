/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Retained.State
import all QuantumAlg.Core.Execution.Local.Retained.Resources
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical restart through one existing retained classical cell

A retained cell changes only the classical record and reference coordinates.
The seed transport works on each complete density block, including arbitrary
external references, before it is applied to the circuit execution.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
  (code : Circuit model ctx ctx) (supported : code.IsLocal)
  (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)

private theorem pureKet_fullSelection_of_reindex_first_at {count : Nat}
    (layout : QuantumLayout count) {Reference EncodedReference : Register}
    (state : DensityOperator (Register.prod layout.register Reference))
    (basis : (Register.prod layout.register Reference).Index ≃
      (Register.prod layout.register EncodedReference).Index)
    (first : ∀ input, (basis input).1 = input.1)
    (selection : Finset (Fin count)) (fullSelection : selection = Finset.univ)
    (seed : layout.SelectedBasis selection)
    (promised : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout selection EncodedReference
        (state.reindex basis))) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout selection Reference state) := by
  cases fullSelection
  exact StatePromise.pureKet_fullSelection_of_reindex_first
    layout state basis first seed promised

/-- An exact one-cell split transfers the same fixed pure seed to the physical
conditioned block, for arbitrary reference and hidden history. -/
theorem underRetained_pureSeed_of_splitBlock
    (noBorrowed : ctx.borrowedQuantumWires = [])
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × H))
    (label : Store (ctx.addRetained key shape fresh) × (model.HiddenState × H))
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (sourcePromise : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection ctx.quantumLayout ctx.borrowedSelectionᶜ _
        ((underRetainedSplitState key shape fresh state).block
          (underRetainedSplitRecords key shape fresh model.HiddenState H label)))) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection
        (ctx.addRetained key shape fresh).quantumLayout
        (ctx.addRetained key shape fresh).borrowedSelectionᶜ Reference
        (state.block label)) := by
  have targetPromise :
      (StatePromise.pure (NormalizedVector.ket seed)).Holds
        (DensityOperator.observeSelection ctx.quantumLayout ctx.borrowedSelectionᶜ _
          ((state.block label).reindex (underRetainedSplitBasis key shape fresh Reference))) := by
    rw [underRetainedSplitState_block_at] at sourcePromise
    exact sourcePromise
  have fullSelection : ctx.borrowedSelectionᶜ = Finset.univ := by
    simp [RuntimeCtx.borrowedSelection, noBorrowed]
  have transferred := pureKet_fullSelection_of_reindex_first_at
    ctx.quantumLayout (state.block label)
    (underRetainedSplitBasis key shape fresh Reference)
    (underRetainedSplitBasis_left key shape fresh Reference)
    ctx.borrowedSelectionᶜ fullSelection seed targetPromise
  exact transferred

/-- Relabel one local execution record with the retained cell and corresponding
physical path, without forgetting either history coordinate. -/
private def underRetainedExecutionRecords (H : Type) :
    (Store ctx × (model.HiddenState ×
      ((Store (retainedLocalFrame (kind := model.kind) key shape) × H) × code.Path))) ≃
    (Store ctx × (model.HiddenState ×
      (Store (retainedLocalFrame (kind := model.kind) key shape) ×
        (H × (underRetained code supported key shape fresh).Path)))) :=
  (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr
    ((Equiv.prodAssoc _ _ _).trans
      ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr
        (underRetainedPathEquiv code supported key shape fresh)))))

/-- One-cell splitting of the actual executed state has exactly the source
execution's conditioned density block at the equivalent complete record. -/
private theorem underRetainedExecutionState_block {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference
      (model.HiddenState × H))
    (record : Store ctx × (model.HiddenState ×
      (Store (retainedLocalFrame (kind := model.kind) key shape) ×
        (H × (underRetained code supported key shape fresh).Path)))) :
    (underRetainedSplitState key shape fresh
      ((underRetained code supported key shape fresh).execute Reference state)).block record =
      (code.execute
        (Register.prod (retainedLocalFrame (kind := model.kind) key shape).register Reference)
        (underRetainedSplitState key shape fresh state)).block
          ((underRetainedExecutionRecords code supported key shape fresh H).symm record) := by
  rw [underRetained_execute]
  let output := code.execute
    (Register.prod (retainedLocalFrame (kind := model.kind) key shape).register Reference)
    (underRetainedSplitState key shape fresh state)
  let update :
      (Store ctx × (model.HiddenState ×
        ((Store (retainedLocalFrame (kind := model.kind) key shape) × H) × code.Path))) →
      (Store ctx × (model.HiddenState ×
        (Store (retainedLocalFrame (kind := model.kind) key shape) ×
          (H × (underRetained code supported key shape fresh).Path)))) :=
    fun value => (value.1, (value.2.1,
      (value.2.2.1.1, (value.2.2.1.2,
        underRetainedPathEquiv code supported key shape fresh value.2.2.2))))
  have sameMap : update =
      underRetainedExecutionRecords code supported key shape fresh H := by
    funext original
    rcases original with ⟨store, hidden, ⟨retained, history⟩, originalPath⟩
    rfl
  have sameState :
      output.mapHistory (fun value =>
        (value.1, (value.2.1.1, (value.2.1.2,
          underRetainedPathEquiv code supported key shape fresh value.2.2)))) =
        output.mapClassical
          (underRetainedExecutionRecords code supported key shape fresh H) := by
    unfold State.mapHistory
    exact ExecutionState.executionState_mapClassical_congr_decision output
      update (underRetainedExecutionRecords code supported key shape fresh H)
      (fun original => congrFun sameMap original) _ _
  rw [sameState]
  exact ExecutionState.coordinate_mapClassical_block output
    (underRetainedExecutionRecords code supported key shape fresh H) record

/-- A local reset keeps the same caller-specified owned basis label beside one
retained classical cell, with the cell included in every complete record. -/
theorem underRetained_reinitializedAt
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : ReinitializedAt code seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    ReinitializedAt (underRetained code supported key shape fresh) seed := by
  unfold ReinitializedAt at fixed ⊢
  intro Reference H _ state label
  let extended := underRetained code supported key shape fresh
  let record := underRetainedSplitRecords key shape fresh model.HiddenState
    (H × extended.Path) label
  let sourceRecord :=
    (underRetainedExecutionRecords code supported key shape fresh H).symm record
  let sourceReference :=
    Register.prod (retainedLocalFrame (kind := model.kind) key shape).register Reference
  let sourceInput := underRetainedSplitState key shape fresh state
  have sourcePromise := fixed sourceReference sourceInput sourceRecord
  have blockEq := underRetainedExecutionState_block code supported key shape fresh
    state record
  rw [← blockEq] at sourcePromise
  exact underRetained_pureSeed_of_splitBlock key shape fresh
    noBorrowed (extended.execute Reference state) label seed sourcePromise

/-- A physical restart certificate survives one existing retained classical
cell. The cell and arbitrary external reference remain in the complete output
record, while the same owned quantum seed is fixed before execution. -/
theorem underRetained_restartCleanup
    (cleanup : RestartCleanup code) (noBorrowed : ctx.borrowedQuantumWires = []) :
    RestartCleanup (underRetained code supported key shape fresh) := by
  let extended := underRetained code supported key shape fresh
  have measured : ∀ path : extended.Path, ∃ dimension : model.SystemDimension,
      Resource.Event.measurement dimension ∈ extended.eventTrace path := by
    intro path
    let original := (underRetainedPathEquiv code supported key shape fresh).symm path
    obtain ⟨dimension, present⟩ := cleanup.measured original
    refine ⟨dimension, ?_⟩
    have actual : Resource.Event.measurement dimension ∈
        extended.eventTrace (underRetainedPathEquiv code supported key shape fresh original) := by
      rw [underRetained_eventTrace]
      exact present
    simpa only [original, Equiv.apply_symm_apply] using actual
  have outerNoBorrowed :
      (ctx.addRetained key shape fresh).borrowedQuantumWires = [] := by
    simpa only [RuntimeCtx.borrowedQuantumWires_addRetained] using noBorrowed
  have restores : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : State (ctx.addRetained key shape fresh) Reference
        (model.HiddenState × H)),
      extended.BorrowedRestored Reference state (extended.execute Reference state) := by
    intro Reference H _ state
    exact borrowedRestored_of_noBorrowedQuantum extended outerNoBorrowed Reference state
  obtain ⟨seed, fixed⟩ := cleanup.reinitialized
  refine ⟨measured, restores, ⟨seed, ?_⟩⟩
  exact underRetained_reinitializedAt code supported key shape fresh seed fixed noBorrowed

end

end QuantumAlg.Circuit
