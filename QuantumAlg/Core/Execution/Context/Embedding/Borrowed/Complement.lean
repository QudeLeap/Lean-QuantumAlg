/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Basis
import all QuantumAlg.Core.Execution.Context.Embedding.Borrowed
import all QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Basis
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Physical coordinates discarded by the complete borrowed observation

Only the nonborrowed local wires and nonborrowed complement wires are traced.
The two sets are identified through their actual placement, with all borrowed
systems remaining jointly present [dW19, qcnotes.tex:389,5381].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- Nonborrowed caller positions are exactly the original nonborrowed positions of both sides. -/
def borrowedComplementPositions :
    QuantumLayout.SelectedPosition localCtx.borrowedSelectionᶜ ⊕
      QuantumLayout.SelectedPosition placement.frame.borrowedSelectionᶜ ≃
        QuantumLayout.SelectedPosition caller.borrowedSelectionᶜ :=
  (Equiv.subtypeSum (p := fun index =>
    match index with
    | .inl localIndex => localIndex ∈ localCtx.borrowedSelectionᶜ
    | .inr frameIndex => frameIndex ∈ placement.frame.borrowedSelectionᶜ)).symm.trans
      (placement.positions.subtypeEquiv fun index => by
        cases index with
        | inl index =>
            change index ∈ localCtx.borrowedSelectionᶜ ↔
              placement.position index ∈ caller.borrowedSelectionᶜ
            simpa only [Finset.mem_compl] using
              not_congr (placement.contextEmbedding_local_borrowed_iff index).symm
        | inr index =>
            simpa only [Finset.mem_compl] using
              not_congr (placement.contextEmbedding_frame_borrowed_iff index).symm)

private def borrowedComplementValueType :
    QuantumLayout.SelectedPosition localCtx.borrowedSelectionᶜ ⊕
      QuantumLayout.SelectedPosition placement.frame.borrowedSelectionᶜ → Type
  | .inl index => Fin (localCtx.quantumLayout.wire index.val).dimension
  | .inr index => Fin (placement.frame.quantumLayout.wire index.val).dimension

private def borrowedComplementValueEquiv
    (index : QuantumLayout.SelectedPosition localCtx.borrowedSelectionᶜ ⊕
      QuantumLayout.SelectedPosition placement.frame.borrowedSelectionᶜ) :
    placement.borrowedComplementValueType index ≃
      Fin (caller.quantumLayout.wire (placement.borrowedComplementPositions index).val).dimension :=
  match index with
  | .inl index => finCongr (congrArg PNat.val
      (placement.contextEmbedding_position_dimension index.val).symm)
  | .inr index => finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
      (placement.contextEmbedding_frame_position_wire index.val).symm)

/-- Each summed caller complement basis is the pair of the two original nonborrowed bases. -/
def borrowedComplementBasis :
    localCtx.quantumLayout.ComplementBasis localCtx.borrowedSelection ×
      placement.frame.quantumLayout.ComplementBasis placement.frame.borrowedSelection ≃
        caller.quantumLayout.ComplementBasis caller.borrowedSelection :=
  (Equiv.sumPiEquivProdPi placement.borrowedComplementValueType).symm.trans
    (placement.borrowedComplementPositions.piCongr placement.borrowedComplementValueEquiv)

/-- Nonborrowed local values are transported on their prescribed physical wires. -/
lemma contextEmbedding_borrowedComplementBasis_local_value
    (localValue : localCtx.quantumLayout.ComplementBasis localCtx.borrowedSelection)
    (frameValue : placement.frame.quantumLayout.ComplementBasis placement.frame.borrowedSelection)
    (index : QuantumLayout.SelectedPosition localCtx.borrowedSelectionᶜ) :
    (placement.borrowedComplementBasis (localValue, frameValue)
      (placement.borrowedComplementPositions (.inl index))).val = (localValue index).val := by
  exact congrArg
    (fun value : Fin (caller.quantumLayout.wire
      (placement.borrowedComplementPositions (.inl index)).val).dimension => value.val)
    (Equiv.piCongr_apply_apply
      (W := placement.borrowedComplementValueType)
      (Z := fun position : QuantumLayout.SelectedPosition caller.borrowedSelectionᶜ =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      placement.borrowedComplementPositions placement.borrowedComplementValueEquiv
      ((Equiv.sumPiEquivProdPi placement.borrowedComplementValueType).symm
        (localValue, frameValue)) (.inl index))

/-- Nonborrowed frame values remain on their original physical wires. -/
lemma contextEmbedding_borrowedComplementBasis_frame_value
    (localValue : localCtx.quantumLayout.ComplementBasis localCtx.borrowedSelection)
    (frameValue : placement.frame.quantumLayout.ComplementBasis placement.frame.borrowedSelection)
    (index : QuantumLayout.SelectedPosition placement.frame.borrowedSelectionᶜ) :
    (placement.borrowedComplementBasis (localValue, frameValue)
      (placement.borrowedComplementPositions (.inr index))).val = (frameValue index).val := by
  exact congrArg
    (fun value : Fin (caller.quantumLayout.wire
      (placement.borrowedComplementPositions (.inr index)).val).dimension => value.val)
    (Equiv.piCongr_apply_apply
      (W := placement.borrowedComplementValueType)
      (Z := fun position : QuantumLayout.SelectedPosition caller.borrowedSelectionᶜ =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      placement.borrowedComplementPositions placement.borrowedComplementValueEquiv
      ((Equiv.sumPiEquivProdPi placement.borrowedComplementValueType).symm
        (localValue, frameValue)) (.inr index))

/-- The joint borrowed/complement split reconstructs the exact full physical placement. -/
lemma contextEmbedding_joinBorrowedSelectedBasis
    (localBorrowed : localCtx.quantumLayout.SelectedBasis localCtx.borrowedSelection)
    (frameBorrowed : placement.frame.quantumLayout.SelectedBasis placement.frame.borrowedSelection)
    (localComplement : localCtx.quantumLayout.ComplementBasis localCtx.borrowedSelection)
    (frameComplement :
      placement.frame.quantumLayout.ComplementBasis placement.frame.borrowedSelection) :
    caller.quantumLayout.joinSelectedBasis caller.borrowedSelection
      (placement.borrowedSelectedBasis (localBorrowed, frameBorrowed))
      (placement.borrowedComplementBasis (localComplement, frameComplement)) =
    placement.basis.symm
      (localCtx.quantumLayout.joinSelectedBasis localCtx.borrowedSelection
        localBorrowed localComplement,
      placement.frame.quantumLayout.joinSelectedBasis placement.frame.borrowedSelection
        frameBorrowed frameComplement) := by
  funext index
  obtain ⟨original, rfl⟩ := placement.positions.surjective index
  apply Fin.ext
  cases original with
  | inl index =>
      change (caller.quantumLayout.joinSelectedBasis caller.borrowedSelection
        (placement.borrowedSelectedBasis (localBorrowed, frameBorrowed))
        (placement.borrowedComplementBasis (localComplement, frameComplement))
        (placement.position index)).val =
        (placement.basis.symm
          (localCtx.quantumLayout.joinSelectedBasis localCtx.borrowedSelection
            localBorrowed localComplement,
          placement.frame.quantumLayout.joinSelectedBasis placement.frame.borrowedSelection
            frameBorrowed frameComplement) (placement.position index)).val
      rw [placement.contextEmbedding_join_local_value]
      by_cases member : index ∈ localCtx.borrowedSelection
      · have left := congrArg Fin.val
          (caller.quantumLayout.joinSelectedBasis_selected_value _
            (placement.borrowedSelectedBasis (localBorrowed, frameBorrowed))
            (placement.borrowedComplementBasis (localComplement, frameComplement))
            (placement.borrowedPositions (.inl ⟨index, member⟩)))
        have right := congrArg Fin.val
          (localCtx.quantumLayout.joinSelectedBasis_selected_value _
            localBorrowed localComplement ⟨index, member⟩)
        exact (left.trans (placement.contextEmbedding_borrowedSelectedBasis_local_value
          localBorrowed frameBorrowed ⟨index, member⟩)).trans right.symm
      · let original : QuantumLayout.SelectedPosition localCtx.borrowedSelectionᶜ :=
          ⟨index, Finset.mem_compl.mpr member⟩
        have left := congrArg Fin.val
          (caller.quantumLayout.joinSelectedBasis_complement_value _
            (placement.borrowedSelectedBasis (localBorrowed, frameBorrowed))
            (placement.borrowedComplementBasis (localComplement, frameComplement))
            (placement.borrowedComplementPositions (.inl original)))
        have right := congrArg Fin.val
          (localCtx.quantumLayout.joinSelectedBasis_complement_value _
            localBorrowed localComplement original)
        exact (left.trans (placement.contextEmbedding_borrowedComplementBasis_local_value
          localComplement frameComplement original)).trans right.symm
  | inr index =>
      rw [placement.contextEmbedding_join_frame_value]
      by_cases member : index ∈ placement.frame.borrowedSelection
      · have left := congrArg Fin.val
          (caller.quantumLayout.joinSelectedBasis_selected_value _
            (placement.borrowedSelectedBasis (localBorrowed, frameBorrowed))
            (placement.borrowedComplementBasis (localComplement, frameComplement))
            (placement.borrowedPositions (.inr ⟨index, member⟩)))
        have right := congrArg Fin.val
          (placement.frame.quantumLayout.joinSelectedBasis_selected_value _
            frameBorrowed frameComplement ⟨index, member⟩)
        exact (left.trans (placement.contextEmbedding_borrowedSelectedBasis_frame_value
          localBorrowed frameBorrowed ⟨index, member⟩)).trans right.symm
      · let original : QuantumLayout.SelectedPosition placement.frame.borrowedSelectionᶜ :=
          ⟨index, Finset.mem_compl.mpr member⟩
        have left := congrArg Fin.val
          (caller.quantumLayout.joinSelectedBasis_complement_value _
            (placement.borrowedSelectedBasis (localBorrowed, frameBorrowed))
            (placement.borrowedComplementBasis (localComplement, frameComplement))
            (placement.borrowedComplementPositions (.inr original)))
        have right := congrArg Fin.val
          (placement.frame.quantumLayout.joinSelectedBasis_complement_value _
            frameBorrowed frameComplement original)
        exact (left.trans (placement.contextEmbedding_borrowedComplementBasis_frame_value
          localComplement frameComplement original)).trans right.symm

end

end QuantumAlg.ContextEmbedding
