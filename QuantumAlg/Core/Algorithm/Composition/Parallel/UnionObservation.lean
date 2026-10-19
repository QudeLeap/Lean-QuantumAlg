/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Parallel.Projection
import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Core.Execution.State.Coordinate.Transport

/-!
# The opposite local subsystem is the unchanged physical frame

The two canonical placements use the same real stores and physical wires in
opposite order. Their complete quantum-reference observations therefore agree
after the corresponding tensor and classical-coordinate swaps.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

private def exchangeLabels (A B H : Type) : (A × (B × H)) ≃ (B × (A × H)) where
  toFun value := (value.2.1, (value.1, value.2.2))
  invFun value := (value.2.1, (value.1, value.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def exchangeBasis (L R Reference : Register) :
    (L.prod (R.prod Reference)).Index ≃ (R.prod (L.prod Reference)).Index :=
  exchangeLabels L.Index R.Index Reference.Index

private def exchangeState {A B H : Type} [Fintype A] [Fintype B] [Fintype H]
    {L R Reference : Register}
    (state : ExecutionState (A × (B × H)) (L.prod (R.prod Reference))) :
    ExecutionState (B × (A × H)) (R.prod (L.prod Reference)) :=
  (state.mapClassical (exchangeLabels A B H)).reindex
    (S := R.prod (L.prod Reference)) (exchangeBasis L R Reference)

private lemma exchangeState_inverse {A B H : Type} [Fintype A] [Fintype B] [Fintype H]
    {L R Reference : Register}
    (state : ExecutionState (A × (B × H)) (L.prod (R.prod Reference))) :
    exchangeState (exchangeState state) = state :=
  ExecutionState.coordinate_transport_inverse state (exchangeLabels A B H)
    (exchangeBasis L R Reference)

private lemma exchangeState_project {A B H : Type} [Fintype A] [Fintype B] [Fintype H]
    {L R Reference : Register}
    (state : ExecutionState (A × (B × H)) (L.prod (R.prod Reference))) :
    ((exchangeState state).mapClassical
      (fun record => (record.1, record.2.2))).forgetReferenceFrame =
      state.referenceObservation (fun record => (record.2.1, record.2.2)) := by
  unfold exchangeState ExecutionState.forgetReferenceFrame ExecutionState.referenceObservation
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp, ExecutionState.reindex_trans]
  have basis : (exchangeBasis L R Reference).trans
      (ExecutionState.referenceFrameBasis (R := R) (S := L) (T := Reference)) =
        Equiv.prodComm L.Index (R.prod Reference).Index := by
    apply Equiv.ext
    intro value
    rfl
  rw [basis]
  apply congrArg ExecutionState.marginalLeft
  apply congrArg (fun current : ExecutionState (B × H) (L.prod (R.prod Reference)) =>
    current.reindex (S := (R.prod Reference).prod L)
      (Equiv.prodComm L.Index (R.prod Reference).Index))
  exact ExecutionState.executionState_mapClassical_congr state rfl

variable {kind : ProblemKind} (left right : RuntimeCtx kind)
  (separate : RuntimeCtx.StorageDisjoint left right)
  {Reference : Register} {H : Type} [Fintype H]

omit [Fintype H] in
private lemma union_record_swap :
    (alongUnionRight left right separate).record H =
      ((alongUnion left right separate).record H).trans
        (exchangeLabels (Store left) (Store right) H) := by
  apply Equiv.ext
  intro value
  change (((alongUnionRight left right separate).store value.1).1,
    (((alongUnionRight left right separate).store value.1).2, value.2)) = _
  rw [contextEmbedding_union_store_swap_value]
  rfl

private lemma union_referenceBasis_swap :
    (alongUnionRight left right separate).referenceBasis Reference =
      ((alongUnion left right separate).referenceBasis Reference).trans
        (exchangeBasis left.register right.register Reference) := by
  apply Equiv.ext
  intro value
  change (((alongUnionRight left right separate).basis value.1).1,
    (((alongUnionRight left right separate).basis value.1).2, value.2)) = _
  rw [contextEmbedding_union_basis_swap_value]
  rfl

private lemma union_split_exchange
    (state : State (left.disjointUnion right separate) Reference H) :
    (alongUnionRight left right separate).split state =
      exchangeState ((alongUnion left right separate).split state) := by
  unfold split exchangeState
  rw [union_record_swap, union_referenceBasis_swap,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp, ExecutionState.reindex_trans]
  apply congrArg (fun current : ExecutionState (Store right × (Store left × H))
      ((left.disjointUnion right separate).register.prod Reference) =>
    current.reindex
      (S := right.register.prod (left.register.prod Reference))
      (((alongUnion left right separate).referenceBasis Reference).trans
        (exchangeBasis left.register right.register Reference)))
  exact ExecutionState.executionState_mapClassical_congr state rfl

/-- The right local CQ state is exactly the left placement's entire physical frame. -/
lemma projectState_union_right_eq_frame_left
    (state : State (left.disjointUnion right separate) Reference H) :
    (alongUnionRight left right separate).projectState state =
      (alongUnion left right separate).frameState state := by
  unfold projectState frameState
  rw [union_split_exchange]
  exact exchangeState_project _

/-- The left local CQ state is exactly the right placement's entire physical frame. -/
lemma projectState_union_left_eq_frame_right
    (state : State (left.disjointUnion right separate) Reference H) :
    (alongUnion left right separate).projectState state =
      (alongUnionRight left right separate).frameState state := by
  have reverse : (alongUnion left right separate).split state =
      exchangeState ((alongUnionRight left right separate).split state) := by
    rw [union_split_exchange]
    exact (exchangeState_inverse ((alongUnion left right separate).split state)).symm
  unfold projectState frameState
  rw [reverse]
  exact exchangeState_project _

end

end QuantumAlg.ContextEmbedding
