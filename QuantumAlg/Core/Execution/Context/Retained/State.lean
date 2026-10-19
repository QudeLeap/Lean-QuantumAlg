/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Retained
import all QuantumAlg.Core.Execution.Context.Permutation.State
import all QuantumAlg.Core.Execution.Context.Union.State.Laws
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Exact state coordinates of one resident retained cell

The complete Store and arbitrary quantum-reference state are transported by
an invertible coordinate map, without an allocation or an execution premise.
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

private lemma retainedUnionState_inverse {Reference : Register} {H : Type} [Fintype H]
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

private lemma retainedUnionState_permuted {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)) Reference H) :
    retainedUnionState key shape fresh
      (ContextPermutation.state (retainedLocalPermutation ctx key shape fresh) state) = state :=
  ContextPermutation.state_inverse (retainedLocalPermutation ctx key shape fresh) state

private lemma retainedUnionState_history {Reference : Register} {H K : Type}
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
lemma underRetainedSplitBasis_left (Reference : Register)
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
lemma underRetainedSplitState_entry {Reference : Register} {Hidden H : Type}
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
lemma underRetainedSplitState_block_at {Reference : Register} {Hidden H : Type}
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
lemma underRetainedSplitState_mass {Reference : Register} {Hidden H : Type}
    [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference (Hidden × H)) :
    (underRetainedSplitState key shape fresh state).mass = state.mass := by
  let : DecidableEq (Hidden × H) := Classical.decEq _
  unfold underRetainedSplitState retainedUnionState
  rw [ContextUnion.contextUnion_splitServiceState_mass, ExecutionState.reindex_mass,
    ExecutionState.mapClassical_mass]

end

end QuantumAlg.Circuit
