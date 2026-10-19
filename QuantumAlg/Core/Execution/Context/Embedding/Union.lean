/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Embedding.Selection
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Context.Embedding.References
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Context.Permutation.Store
import all QuantumAlg.Core.Execution.Context.Relabeling.Store
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# The two physical views of one disjoint context union

The left call's frame is the right call's local subsystem and conversely.
Both views retain the same complete storage cells and the same finite values
on the same physical quantum wires. Their full basis and store equivalences
therefore differ only by swapping the two original factors
[dW19, qcnotes.tex:389,5381].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

private lemma split_local_value (value : caller.register.Index)
    (index : Fin localCtx.systemCount) :
    ((placement.basis value).1 index).val = (value (placement.position index)).val := by
  have same := placement.contextEmbedding_join_local_value
    (placement.basis value).1 (placement.basis value).2 index
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using same.symm

private lemma split_frame_value (value : caller.register.Index)
    (index : Fin placement.frame.systemCount) :
    ((placement.basis value).2 index).val =
      (value (placement.positions (.inr index))).val := by
  have same := placement.contextEmbedding_join_frame_value
    (placement.basis value).1 (placement.basis value).2 index
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using same.symm

private def unionFrameInput {shape : CShape} (ref : CInputRef placement.frame shape) :
    CInputRef caller shape :=
  ContextPermutation.input placement.covers (ContextUnion.inputRight placement.separate ref)

private lemma join_frame_read (localStore : Store localCtx)
    (frameStore : Store placement.frame) {shape : CShape}
    (ref : CInputRef placement.frame shape) :
    (placement.store.symm (localStore, frameStore)).read (placement.unionFrameInput ref) =
      frameStore.read ref := by
  change (ContextPermutation.store placement.covers
    (ContextUnion.join placement.separate
      (ContextRelabeling.storeEquiv placement.keys placement.physical localCtx localStore)
      frameStore)).read _ = _
  rw [unionFrameInput, ContextPermutation.store_read_input,
    ContextUnion.contextUnion_read_join_right]

private lemma split_local_read (original : Store caller) {shape : CShape}
    (ref : CInputRef localCtx shape) :
    original.read (placement.input ref) = (placement.store original).1.read ref := by
  have same := placement.contextEmbedding_input_read
    (placement.store original).1 (placement.store original).2 ref
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using same

private lemma split_frame_read (original : Store caller) {shape : CShape}
    (ref : CInputRef placement.frame shape) :
    original.read (placement.unionFrameInput ref) = (placement.store original).2.read ref := by
  have same := placement.join_frame_read
    (placement.store original).1 (placement.store original).2 ref
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using same

variable (left right : RuntimeCtx kind) (separate : RuntimeCtx.StorageDisjoint left right)

/-- A left local wire and the right call's corresponding frame wire have one physical position. -/
lemma contextEmbedding_union_left_position (index : Fin left.systemCount) :
    (alongUnion left right separate).position index =
      (alongUnionRight left right separate).positions (.inr index) := by
  apply (left.disjointUnion right separate).quantumLayout.position_eq_of_identity_eq
  have localWire : (left.disjointUnion right separate).quantumLayout.wire
      ((alongUnion left right separate).position index) = left.quantumLayout.wire index :=
    (alongUnion left right separate).contextEmbedding_position_wire index
  have frameWire : (left.disjointUnion right separate).quantumLayout.wire
      ((alongUnionRight left right separate).positions (.inr index)) =
        left.quantumLayout.wire index :=
    (alongUnionRight left right separate).contextEmbedding_frame_position_wire index
  exact congrArg QuantumWire.identity (localWire.trans frameWire.symm)

/-- A right local wire is precisely the left call's unchanged frame wire. -/
lemma contextEmbedding_union_right_position (index : Fin right.systemCount) :
    (alongUnion left right separate).positions (.inr index) =
      (alongUnionRight left right separate).position index := by
  apply (left.disjointUnion right separate).quantumLayout.position_eq_of_identity_eq
  have frameWire : (left.disjointUnion right separate).quantumLayout.wire
      ((alongUnion left right separate).positions (.inr index)) = right.quantumLayout.wire index :=
    (alongUnion left right separate).contextEmbedding_frame_position_wire index
  have localWire : (left.disjointUnion right separate).quantumLayout.wire
      ((alongUnionRight left right separate).position index) = right.quantumLayout.wire index :=
    (alongUnionRight left right separate).contextEmbedding_position_wire index
  exact congrArg QuantumWire.identity (frameWire.trans localWire.symm)

/-- The two canonical physical basis maps keep identical finite values in opposite order. -/
lemma contextEmbedding_union_basis_swap_value
    (value : (left.disjointUnion right separate).register.Index) :
    (alongUnionRight left right separate).basis value =
      ((alongUnion left right separate).basis value).swap := by
  apply Prod.ext
  · change ((alongUnionRight left right separate).basis value).1 =
      ((alongUnion left right separate).basis value).2
    funext index
    apply Fin.ext
    exact ((alongUnionRight left right separate).split_local_value value index).trans
      ((congrArg (fun position => (value position).val)
        (contextEmbedding_union_right_position left right separate index).symm).trans
          ((alongUnion left right separate).split_frame_value value index).symm)
  · change ((alongUnionRight left right separate).basis value).2 =
      ((alongUnion left right separate).basis value).1
    funext index
    apply Fin.ext
    exact ((alongUnionRight left right separate).split_frame_value value index).trans
      ((congrArg (fun position => (value position).val)
        (contextEmbedding_union_left_position left right separate index).symm).trans
          ((alongUnion left right separate).split_local_value value index).symm)

/-- Canonical left and right physical coordinates differ only by the actual tensor swap. -/
lemma contextEmbedding_union_basis_swap :
    (alongUnionRight left right separate).basis =
      (alongUnion left right separate).basis.trans
        (Equiv.prodComm left.register.Index right.register.Index) := by
  apply Equiv.ext
  intro value
  exact contextEmbedding_union_basis_swap_value left right separate value

/-- The two canonical store maps retain all original cells in opposite factor order. -/
lemma contextEmbedding_union_store_swap_value
    (original : Store (left.disjointUnion right separate)) :
    (alongUnionRight left right separate).store original =
      ((alongUnion left right separate).store original).swap := by
  apply Prod.ext
  · change ((alongUnionRight left right separate).store original).1 =
      ((alongUnion left right separate).store original).2
    apply Store.store_eq_of_storage_reads
    intro shape ref
    calc
      _ = original.read ((alongUnionRight left right separate).input (.storage ref)) :=
        ((alongUnionRight left right separate).split_local_read original (.storage ref)).symm
      _ = original.read ((alongUnion left right separate).unionFrameInput (.storage ref)) := by
        apply congrArg original.read
        change CInputRef.storage _ = CInputRef.storage _
        apply congrArg CInputRef.storage
        exact CStorageRef.storageRef_eq_of_key _ _ rfl
      _ = _ := (alongUnion left right separate).split_frame_read original (.storage ref)
  · change ((alongUnionRight left right separate).store original).2 =
      ((alongUnion left right separate).store original).1
    apply Store.store_eq_of_storage_reads
    intro shape ref
    calc
      _ = original.read ((alongUnionRight left right separate).unionFrameInput (.storage ref)) :=
        ((alongUnionRight left right separate).split_frame_read original (.storage ref)).symm
      _ = original.read ((alongUnion left right separate).input (.storage ref)) := by
        apply congrArg original.read
        change CInputRef.storage _ = CInputRef.storage _
        apply congrArg CInputRef.storage
        exact CStorageRef.storageRef_eq_of_key _ _ rfl
      _ = _ := (alongUnion left right separate).split_local_read original (.storage ref)

/-- The opposite service placement observes exactly the original other-side store. -/
lemma contextEmbedding_union_store_swap :
    (alongUnionRight left right separate).store =
      (alongUnion left right separate).store.trans (Equiv.prodComm (Store left) (Store right)) := by
  apply Equiv.ext
  intro original
  exact contextEmbedding_union_store_swap_value left right separate original

end

end QuantumAlg.ContextEmbedding
