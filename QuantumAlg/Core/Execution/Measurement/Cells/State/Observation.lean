/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.State
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Density
import all QuantumAlg.Core.Execution.Measurement.Readout.Effect

/-!
# The same readout event beside existing measurement cells

The actual retained Stores become history only in exact proof coordinates.
Their zero-wire registers remain beside the complete external reference.
Neither transformation changes any finite value on the observed physical
wires, so the same event has exactly the same weight. No old cell value,
product-state, normalization or qubit-dimension premise is needed.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma marginal_reindex {C : Type} [Fintype C] {R S : Register}
    (state : ExecutionState C R) (basis : R.Index ≃ S.Index) :
    (state.reindex basis).quantumMarginal = state.quantumMarginal.reindex basis := by
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.quantumMarginal, Matrix.sum_apply,
    ExecutionState.reindex_block_entry, DensityOperator.reindex_entry]

private lemma event_reindex {source target : RuntimeCtx .quantum} {width : Nat}
    {Reference Other : Register}
    (basis : (source.register.prod Reference).Index ≃ (target.register.prod Other).Index)
    (beforeWires : Fin width → Fin source.systemCount)
    (afterWires : Fin width → Fin target.systemCount)
    (values : ∀ input index, ((basis input).1 (afterWires index)).val =
      (input.1 (beforeWires index)).val)
    (event : (Fin width → Bool) → Bool)
    (state : DensityOperator (source.register.prod Reference)) :
    (QubitReadouts.eventEffect beforeWires event Reference).weight state =
      (QubitReadouts.eventEffect afterWires event Other).weight (state.reindex basis) := by
  rw [QubitReadouts.eventEffect_weight, QubitReadouts.eventEffect_weight]
  apply congrArg Complex.re
  rw [← basis.sum_comp]
  apply Finset.sum_congr rfl
  intro input _
  simp only [DensityOperator.reindex_entry, Equiv.symm_apply_apply, values]

private def retainedReadoutBasis (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys) (Reference : Register) :
    ((ctx.addRetained key shape fresh).register.prod Reference).Index ≃
      (ctx.register.prod
        ((retainedLocalFrame (kind := .quantum) key shape).register.prod Reference)).Index :=
  (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
    Reference).symm.trans
      (ContextUnion.referenceBasis ctx (retainedLocalFrame (kind := .quantum) key shape)
        (retainedLocalDisjoint ctx key shape fresh) Reference)

private lemma retainedReadoutBasis_value (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys) (Reference : Register)
    (input : ((ctx.addRetained key shape fresh).register.prod Reference).Index)
    (wire : Fin ctx.systemCount) :
    ((retainedReadoutBasis ctx key shape fresh Reference input).1 wire).val =
      (input.1 wire).val := by
  let frame := retainedLocalFrame (kind := .quantum) key shape
  let separate := retainedLocalDisjoint ctx key shape fresh
  let same := retainedLocalPermutation ctx key shape fresh
  let inUnion := ContextUnion.leftPosition ctx frame separate wire
  have position : ContextPermutation.positions same inUnion = wire := by
    apply (ctx.addRetained key shape fresh).quantumLayout.position_eq_of_identity_eq
    exact congrArg QuantumWire.identity ((ContextPermutation.positions_wire same inUnion).trans
      (ContextUnion.contextUnion_left_wire ctx frame separate wire))
  change ((ContextUnion.unionBasisEquiv ctx frame separate
    ((ContextPermutation.basis same).symm input.1)).1 wire).val = _
  calc
    _ = ((ContextPermutation.basis same).symm input.1 inUnion).val :=
      (ContextUnion.contextUnion_split_left_value ctx frame separate _ wire).symm
    _ = (ContextPermutation.basis same ((ContextPermutation.basis same).symm input.1)
        (ContextPermutation.positions same inUnion)).val :=
      (ContextPermutation.basis_value same _ inUnion).symm
    _ = (input.1 wire).val := by rw [Equiv.apply_symm_apply, position]

private lemma retainedSplit_marginal (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys) {Reference : Register}
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H)) :
    (underRetainedSplitState key shape fresh state).quantumMarginal =
      state.quantumMarginal.reindex (retainedReadoutBasis ctx key shape fresh Reference) := by
  unfold underRetainedSplitState retainedReadoutBasis
  rw [ContextUnion.contextUnion_splitServiceState_quantumMarginal]
  unfold retainedUnionState
  erw [marginal_reindex]
  simp only [ExecutionState.mapClassical_quantumMarginal, DensityOperator.reindex_trans]

private lemma retained_eventEffectWeight (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys) {width : Nat}
    (wires : Fin width → Fin ctx.systemCount) {Reference : Register}
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H))
    (event : (Fin width → Bool) → Bool) :
    (QubitReadouts.eventEffect (ctx := ctx.addRetained key shape fresh) wires event
      Reference).weight
        state.quantumMarginal =
      (QubitReadouts.eventEffect wires event
        ((retainedLocalFrame (kind := .quantum) key shape).register.prod Reference)).weight
          (underRetainedSplitState key shape fresh state).quantumMarginal := by
  rw [retainedSplit_marginal]
  exact event_reindex (retainedReadoutBasis ctx key shape fresh Reference) wires wires
    (fun input index => retainedReadoutBasis_value ctx key shape fresh Reference input
      (wires index))
    event state.quantumMarginal

/-- The actual readout event keeps its weight through all existing-cell coordinates. -/
lemma underMeasurementCells_eventEffectWeight (ctx : RuntimeCtx .quantum) (count : Nat)
    {width : Nat} (wires : Fin width → Fin ctx.systemCount) {Reference : Register}
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (MeasurementCells.context ctx 2 count) Reference (Hidden × H))
    (event : (Fin width → Bool) → Bool) :
    (QubitReadouts.eventEffect (fun index => MeasurementCells.wireEquiv ctx 2 count (wires index))
      event Reference).weight state.quantumMarginal =
      (QubitReadouts.eventEffect wires event
        (measurementCellsReference ctx 2 count Reference)).weight
        (underMeasurementCellsSplitState ctx 2 count state).quantumMarginal := by
  induction count generalizing Reference H with
  | zero =>
      simp only [MeasurementCells.wireEquiv, Equiv.refl_apply, measurementCellsReference,
        underMeasurementCellsSplitState, State.mapHistory_quantumMarginal]
  | succ count ih =>
      let inner := MeasurementCells.context ctx 2 count
      have next := retained_eventEffectWeight inner inner.canonicalFreshKey (.finite 2)
        inner.canonicalFreshKey_fresh
        (fun index => MeasurementCells.wireEquiv ctx 2 count (wires index)) state event
      have rest := ih (underRetainedSplitState inner.canonicalFreshKey (.finite 2)
        inner.canonicalFreshKey_fresh state)
      simp only [underMeasurementCellsSplitState, measurementCellsReference]
      erw [State.mapHistory_quantumMarginal]
      exact next.trans rest

end

end QuantumAlg.Circuit
