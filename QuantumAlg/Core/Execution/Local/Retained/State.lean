/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Retained
import all QuantumAlg.Core.Execution.Context.Permutation.Local.State
import all QuantumAlg.Core.Execution.Local.Framing.State
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete local execution beside arbitrary retained data

The actual existing retained head is separated only in mathematical Store and
basis coordinates. Its value, history and every quantum-reference correlation
are preserved through the original interpreter. No initial-value, preparation
or support hypothesis is needed [dW19, qcnotes.tex:5381,5405,5409].
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}
  (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)

private def retainedUnionState {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference H) :
    State (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)) Reference H :=
  (state.mapClassical
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) H).symm).reindex
      (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
        Reference).symm

private theorem retainedUnionState_inverse {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference H) :
    ContextPermutation.state (retainedLocalPermutation ctx key shape fresh)
      (retainedUnionState key shape fresh state) = state := by
  have inverse := ExecutionState.coordinate_transport_inverse
    (S := (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)).register.prod Reference) state
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) H).symm
    (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
      Reference).symm
  simpa only [ContextPermutation.state, retainedUnionState, Equiv.symm_symm] using inverse

private theorem retainedUnionState_permuted {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)) Reference H) :
    retainedUnionState key shape fresh
      (ContextPermutation.state (retainedLocalPermutation ctx key shape fresh) state) = state :=
  ContextPermutation.state_inverse (retainedLocalPermutation ctx key shape fresh) state

private theorem retainedUnionState_history {Reference : Register} {H K : Type}
    [Fintype H] [Fintype K]
    (state : State (ctx.addRetained key shape fresh) Reference H) (update : H → K) :
    retainedUnionState key shape fresh (state.mapHistory update) =
      (retainedUnionState key shape fresh state).mapHistory update := by
  unfold retainedUnionState State.mapHistory
  exact ExecutionState.coordinate_transport_diagram state
    (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
      Reference).symm
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) H).symm
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) K).symm
    (fun record => (record.1, update record.2))
    (fun record => (record.1, update record.2)) (fun _ => rfl)

/-- Split the existing retained head while keeping its value and persistent service. -/
def underRetainedSplitState {Reference : Register} {Hidden H : Type}
    [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H)) :
    State ctx (Register.prod (retainedLocalFrame (kind := kind) key shape).register Reference)
      (Hidden × (Store (retainedLocalFrame (kind := kind) key shape) × H)) :=
  ContextUnion.splitServiceState ctx (retainedLocalFrame (kind := kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh) (retainedUnionState key shape fresh state)

/-- The exact complete basis correspondence when a retained classical cell is
placed in the mathematical reference coordinate. -/
def underRetainedSplitBasis (Reference : Register) :
    (Register.prod (ctx.addRetained key shape fresh).register Reference).Index ≃
      (Register.prod ctx.register
        (Register.prod (retainedLocalFrame (kind := kind) key shape).register Reference)).Index :=
  (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
    Reference).symm.trans
      (ContextUnion.referenceBasis ctx (retainedLocalFrame (kind := kind) key shape)
        (retainedLocalDisjoint ctx key shape fresh) Reference)

/-- Retaining classical storage cannot change any physical quantum-wire value
under the exact complete basis coordinate change. -/
theorem underRetainedSplitBasis_left (Reference : Register)
    (input : (Register.prod (ctx.addRetained key shape fresh).register Reference).Index) :
    (underRetainedSplitBasis key shape fresh Reference input).1 = input.1 := by
  funext wire
  apply Fin.ext
  let frame := retainedLocalFrame (kind := kind) key shape
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

/-- The matching complete store, service, and history correspondence. -/
def underRetainedSplitRecords (Hidden H : Type) :
    (Store (ctx.addRetained key shape fresh) × (Hidden × H)) ≃
      (Store ctx × (Hidden ×
        (Store (retainedLocalFrame (kind := kind) key shape) × H))) :=
  (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh)
    (Hidden × H)).symm.trans
      ((ContextUnion.recordEquiv ctx (retainedLocalFrame (kind := kind) key shape)
        (retainedLocalDisjoint ctx key shape fresh) (Hidden × H)).trans
        ((Equiv.refl (Store ctx)).prodCongr
          (ContextUnion.serviceHistory (retainedLocalFrame (kind := kind) key shape)
            Hidden H)))

/-- Every complete density-matrix entry is retained, including off-diagonal
external-reference correlations and zero-weight classical records. -/
theorem underRetainedSplitState_entry {Reference : Register} {Hidden H : Type}
    [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H))
    (label : Store ctx × (Hidden ×
      (Store (retainedLocalFrame (kind := kind) key shape) × H)))
    (row column : (Register.prod ctx.register
      (Register.prod (retainedLocalFrame (kind := kind) key shape).register Reference)).Index) :
    ((underRetainedSplitState key shape fresh state).block label).matrix row column =
      (state.block ((underRetainedSplitRecords key shape fresh Hidden H).symm label)).matrix
        ((underRetainedSplitBasis key shape fresh Reference).symm row)
        ((underRetainedSplitBasis key shape fresh Reference).symm column) := by
  let : DecidableEq (Hidden × H) := Classical.decEq _
  let split := ContextUnion.splitState ctx (retainedLocalFrame (kind := kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh)
    (retainedUnionState key shape fresh state)
  let service := ContextUnion.serviceHistory (retainedLocalFrame (kind := kind) key shape)
    Hidden H
  let labels := (Equiv.refl (Store ctx)).prodCongr service
  have sameMap : split.mapHistory service = split.mapClassical labels := by
    unfold State.mapHistory
    exact ExecutionState.executionState_mapClassical_congr_decision split
      _ labels (fun _ => rfl) _ _
  unfold underRetainedSplitState ContextUnion.splitServiceState
  change ((split.mapHistory service).block label).matrix row column = _
  rw [sameMap]
  rw [ExecutionState.coordinate_mapClassical_block]
  rw [ContextUnion.contextUnion_splitState_entry]
  unfold retainedUnionState
  rw [ExecutionState.reindex_block_entry]
  rw [ExecutionState.coordinate_mapClassical_block]
  rfl

/-- One existing retained cell preserves every complete conditioned density
block under its exact store and quantum-reference coordinate maps. -/
theorem underRetainedSplitState_block_at {Reference : Register} {Hidden H : Type}
    [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H))
    (label : Store (ctx.addRetained key shape fresh) × (Hidden × H)) :
    (underRetainedSplitState key shape fresh state).block
      (underRetainedSplitRecords key shape fresh Hidden H label) =
        (state.block label).reindex (underRetainedSplitBasis key shape fresh Reference) := by
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry]
  have entry := underRetainedSplitState_entry key shape fresh state
    (underRetainedSplitRecords key shape fresh Hidden H label) row column
  simpa only [Equiv.symm_apply_apply] using entry

/-- Splitting an existing retained cell preserves the mass of the complete state. -/
theorem underRetainedSplitState_mass {Reference : Register} {Hidden H : Type}
    [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H)) :
    (underRetainedSplitState key shape fresh state).mass = state.mass := by
  let : DecidableEq (Hidden × H) := Classical.decEq _
  unfold underRetainedSplitState retainedUnionState
  rw [ContextUnion.contextUnion_splitServiceState_mass, ExecutionState.reindex_mass,
    ExecutionState.mapClassical_mass]

/-- The full actual state obeys the original local execution after exact retained-cell splitting. -/
theorem underRetained_execute {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (code : Circuit model ctx ctx) (supported : code.IsLocal)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × H)) :
    underRetainedSplitState key shape fresh
        ((underRetained code supported key shape fresh).execute Reference state) =
      (code.execute
        (Register.prod (retainedLocalFrame (kind := model.kind) key shape).register Reference)
        (underRetainedSplitState key shape fresh state)).mapHistory
          (fun record => (record.1, (record.2.1.1,
            (record.2.1.2,
              underRetainedPathEquiv code supported key shape fresh record.2.2)))) := by
  let original := retainedUnionState key shape fresh state
  let framed := retainedFramed code supported key shape fresh
  let permutation := retainedLocalPermutation ctx key shape fresh
  let pathMap : framed.Path ≃ (underRetained code supported key shape fresh).Path :=
    ContextPermutation.localPathEquiv framed
    (retainedFramed_isLocal code supported key shape fresh)
    (ctx.addRetained key shape fresh) permutation
  have permuted :
      (underRetained code supported key shape fresh).execute Reference
          (ContextPermutation.state permutation original) =
        (ContextPermutation.state permutation (framed.execute Reference original)).mapHistory
          (fun record => (record.1, (record.2.1, pathMap record.2.2))) :=
    ContextPermutation.localCircuit_execute framed
      (retainedFramed_isLocal code supported key shape fresh)
      (ctx.addRetained key shape fresh) permutation Reference original
  have restored : ContextPermutation.state permutation original = state :=
    retainedUnionState_inverse key shape fresh state
  rw [restored] at permuted
  have actual :
      retainedUnionState key shape fresh
          ((underRetained code supported key shape fresh).execute Reference state) =
        (framed.execute Reference original).mapHistory
          (fun record => (record.1, (record.2.1, pathMap record.2.2))) := by
    rw [permuted, retainedUnionState_history, retainedUnionState_permuted]
  change ContextUnion.splitServiceState ctx (retainedLocalFrame (kind := model.kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh)
    (retainedUnionState key shape fresh
      ((underRetained code supported key shape fresh).execute Reference state)) = _
  rw [actual]
  erw [ContextUnion.contextUnion_splitServiceState_mapHistory ctx
    (retainedLocalFrame (kind := model.kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh) (framed.execute Reference original)
    (fun record : H × framed.Path => (record.1, pathMap record.2))]
  let frameMap : code.Path ≃ framed.Path :=
    ContextUnion.frameLocalPathEquiv code supported (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh)
  have localExecution :
      ContextUnion.splitServiceState ctx (retainedLocalFrame (kind := model.kind) key shape)
          (retainedLocalDisjoint ctx key shape fresh) (framed.execute Reference original) =
        (code.execute
          (Register.prod (retainedLocalFrame (kind := model.kind) key shape).register Reference)
          (ContextUnion.splitServiceState ctx (retainedLocalFrame key shape)
            (retainedLocalDisjoint ctx key shape fresh) original)).mapHistory
              (fun record => (record.1, (record.2.1.1, (record.2.1.2, frameMap record.2.2)))) :=
    ContextUnion.frameLocal_execute code supported
      (retainedLocalFrame (kind := model.kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh) Reference original
  rw [localExecution, State.mapHistory_comp]
  rfl

end

end QuantumAlg.Circuit
