/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Core.Execution.Context.Union.State.Laws
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence

/-!
# Full native execution beside an existing disjoint frame

Identity wire and storage placement agrees with the original complete union
coordinates. The frame Store, persistent service, every old history and the
arbitrary quantum reference remain in the exact execution equality.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Canonical physical embedding reads exactly the original appended basis coordinates. -/
lemma alongUnion_basis {kind : ProblemKind} (localCtx frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint localCtx frame) :
    (ContextEmbedding.alongUnion localCtx frame separate).basis =
      ContextUnion.unionBasisEquiv localCtx frame separate := by
  let placement := ContextEmbedding.alongUnion localCtx frame separate
  have localPosition (index : Fin localCtx.systemCount) :
      placement.position index = ContextUnion.leftPosition localCtx frame separate index := by
    apply (localCtx.disjointUnion frame separate).quantumLayout.position_eq_of_identity_eq
    exact (congrArg QuantumWire.identity
      (placement.contextEmbedding_position_wire index)).trans
        (congrArg QuantumWire.identity
          (ContextUnion.contextUnion_left_wire localCtx frame separate index)).symm
  have framePosition (index : Fin frame.systemCount) :
      placement.positions (.inr index) =
        ContextUnion.rightPosition localCtx frame separate index := by
    apply (localCtx.disjointUnion frame separate).quantumLayout.position_eq_of_identity_eq
    exact (congrArg QuantumWire.identity
      (placement.contextEmbedding_frame_position_wire index)).trans
        (congrArg QuantumWire.identity
          (ContextUnion.contextUnion_right_wire localCtx frame separate index)).symm
  apply Equiv.ext
  intro value
  apply Prod.ext
  · funext index
    apply Fin.ext
    have actual := placement.split_local_value value index
    rw [localPosition] at actual
    exact actual.trans (ContextUnion.contextUnion_split_left_value
      localCtx frame separate value index)
  · funext index
    apply Fin.ext
    have actual := placement.split_frame_value value index
    rw [framePosition index] at actual
    exact actual.trans (ContextUnion.contextUnion_split_right_value
      localCtx frame separate value index)

/-- Identity key placement retains exactly both original finite Store vectors. -/
lemma alongUnion_store {kind : ProblemKind} (localCtx frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint localCtx frame) :
    (ContextEmbedding.alongUnion localCtx frame separate).store =
      ContextUnion.storeEquiv separate := by
  let placement := ContextEmbedding.alongUnion localCtx frame separate
  apply Equiv.ext
  intro original
  apply Prod.ext
  · apply Store.store_eq_of_storage_reads
    intro shape ref
    have sameInput : placement.input (.storage ref) =
        ContextUnion.inputLeft separate (.storage ref) := by
      change CInputRef.storage _ = CInputRef.storage _
      apply congrArg CInputRef.storage
      exact CStorageRef.storageRef_eq_of_key _ _ rfl
    calc
      _ = original.read (placement.input (.storage ref)) :=
        (placement.split_local_read original (.storage ref)).symm
      _ = original.read (ContextUnion.inputLeft separate (.storage ref)) :=
        congrArg original.read sameInput
      _ = ((ContextUnion.storeEquiv separate).symm
          ((ContextUnion.storeEquiv separate) original)).read
            (ContextUnion.inputLeft separate (.storage ref)) :=
        congrArg (fun stored => stored.read (ContextUnion.inputLeft separate (.storage ref)))
          ((ContextUnion.storeEquiv separate).symm_apply_apply original).symm
      _ = _ := ContextUnion.contextUnion_read_join_left separate
        ((ContextUnion.storeEquiv separate original).1)
        ((ContextUnion.storeEquiv separate original).2) (.storage ref)
  · apply Store.store_eq_of_storage_reads
    intro shape ref
    have sameInput : placement.unionFrameInput (.storage ref) =
        ContextUnion.inputRight separate (.storage ref) := by
      change CInputRef.storage _ = CInputRef.storage _
      apply congrArg CInputRef.storage
      exact CStorageRef.storageRef_eq_of_key _ _ rfl
    calc
      _ = original.read (placement.unionFrameInput (.storage ref)) :=
        (placement.split_frame_read original (.storage ref)).symm
      _ = original.read (ContextUnion.inputRight separate (.storage ref)) :=
        congrArg original.read sameInput
      _ = ((ContextUnion.storeEquiv separate).symm
          ((ContextUnion.storeEquiv separate) original)).read
            (ContextUnion.inputRight separate (.storage ref)) :=
        congrArg (fun stored => stored.read (ContextUnion.inputRight separate (.storage ref)))
          ((ContextUnion.storeEquiv separate).symm_apply_apply original).symm
      _ = _ := ContextUnion.contextUnion_read_join_right separate
        ((ContextUnion.storeEquiv separate original).1)
        ((ContextUnion.storeEquiv separate original).2) (.storage ref)

/-- The same full local/frame/external-reference associator follows from the physical basis law. -/
lemma alongUnion_referenceBasis {kind : ProblemKind} (localCtx frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint localCtx frame) (Reference : Register) :
    (ContextEmbedding.alongUnion localCtx frame separate).referenceBasis Reference =
      ContextUnion.referenceBasis localCtx frame separate Reference := by
  unfold ContextEmbedding.referenceBasis ContextUnion.referenceBasis
  rw [alongUnion_basis]
  rfl

/-- Native split coordinates are exactly the original full union service coordinates. -/
lemma alongUnion_splitServiceState {kind : ProblemKind} (localCtx frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint localCtx frame) {Reference : Register}
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (localCtx.disjointUnion frame separate) Reference (Hidden × H)) :
    ContextUnion.splitServiceState localCtx frame separate state =
      ((ContextEmbedding.alongUnion localCtx frame separate).split state).mapHistory
        (fun record => (record.2.1, (record.1, record.2.2))) := by
  have records : (ContextEmbedding.alongUnion localCtx frame separate).record (Hidden × H) =
      ContextUnion.recordEquiv localCtx frame separate (Hidden × H) := by
    unfold ContextEmbedding.record ContextUnion.recordEquiv
    rw [alongUnion_store]
    rfl
  unfold ContextUnion.splitServiceState ContextUnion.splitState ContextEmbedding.split
  rw [records, alongUnion_referenceBasis]
  rfl

end

end QuantumAlg.ContextEmbedding

namespace QuantumAlg.Circuit

noncomputable section

open Execution

/-- An allocation-free child retains the complete disjoint frame on its original path. -/
lemma union_embed_execute {model : ExecutionModel} {localCtx : RuntimeCtx model.kind}
    {allowAllocation : Bool} (code : Circuit model localCtx localCtx false)
    (environment : model.Environment)
    (frame : RuntimeCtx model.kind) (separate : RuntimeCtx.StorageDisjoint localCtx frame)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State (localCtx.disjointUnion frame separate) Reference (model.HiddenState × H)) :
    ContextUnion.splitServiceState localCtx frame separate
      ((Circuit.embed (allowAllocation := allowAllocation)
        (ContextEmbedding.alongUnion localCtx frame separate) code).execute environment
          Reference state) =
      (code.execute environment (Register.prod frame.register Reference)
        (ContextUnion.splitServiceState localCtx frame separate state)).mapHistory
          (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  classical
  rw [ContextEmbedding.alongUnion_splitServiceState,
    ContextEmbedding.alongUnion_splitServiceState]
  exact Circuit.split_execute_embed_history (allowAllocation := allowAllocation)
    (ContextEmbedding.alongUnion localCtx frame separate) code environment Reference state

end

end QuantumAlg.Circuit
