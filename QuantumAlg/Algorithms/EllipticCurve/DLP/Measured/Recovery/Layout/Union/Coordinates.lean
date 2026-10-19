/- Exact coordinates of the physical context union. -/

module

import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Core.Execution.Context.Union.State

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

open QuantumAlg QuantumAlg.Execution

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

/-- The complete frame Store and mathematical history retain the same original labels. -/
lemma alongUnion_record {kind : ProblemKind} (localCtx frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint localCtx frame) (History : Type) :
    (ContextEmbedding.alongUnion localCtx frame separate).record History =
      ContextUnion.recordEquiv localCtx frame separate History := by
  unfold ContextEmbedding.record ContextUnion.recordEquiv
  rw [alongUnion_store]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
