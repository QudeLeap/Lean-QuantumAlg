/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Borrowed
public import QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Context.Embedding.Borrowed
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Borrowed
import Mathlib.Logic.Equiv.Prod

/-!
# Borrowed basis coordinates through physical placement

The complete caller borrowed register splits into the original local and
complement borrowed registers. The finite value correspondence is determined
wire by wire by the actual execution placement. Restricting a full basis
commutes with this correspondence, including every borrowed dimension
[dW19, qcnotes.tex:389,5381].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

private def borrowedValueType :
    QuantumLayout.SelectedPosition localCtx.borrowedSelection ⊕
      QuantumLayout.SelectedPosition placement.frame.borrowedSelection → Type
  | .inl index => Fin (localCtx.quantumLayout.wire index.val).dimension
  | .inr index => Fin (placement.frame.quantumLayout.wire index.val).dimension

private def borrowedValueEquiv
    (index : QuantumLayout.SelectedPosition localCtx.borrowedSelection ⊕
      QuantumLayout.SelectedPosition placement.frame.borrowedSelection) :
    placement.borrowedValueType index ≃
      Fin (caller.quantumLayout.wire (placement.borrowedPositions index).val).dimension := by
  cases index with
  | inl index =>
      exact finCongr (congrArg PNat.val
        (placement.contextEmbedding_position_dimension index.val).symm)
  | inr index =>
      exact finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
        (placement.contextEmbedding_frame_position_wire index.val).symm)

/-- Assemble the selected borrowed values on the actual caller positions. -/
def borrowedSelectedBasis :
    localCtx.quantumLayout.SelectedBasis localCtx.borrowedSelection ×
      placement.frame.quantumLayout.SelectedBasis placement.frame.borrowedSelection ≃
        caller.quantumLayout.SelectedBasis caller.borrowedSelection :=
  (Equiv.sumPiEquivProdPi placement.borrowedValueType).symm.trans
    (placement.borrowedPositions.piCongr placement.borrowedValueEquiv)

/-- Every local borrowed finite value reaches its original placed physical wire. -/
lemma contextEmbedding_borrowedSelectedBasis_local_value
    (localValue : localCtx.quantumLayout.SelectedBasis localCtx.borrowedSelection)
    (frameValue : placement.frame.quantumLayout.SelectedBasis placement.frame.borrowedSelection)
    (index : QuantumLayout.SelectedPosition localCtx.borrowedSelection) :
    (placement.borrowedSelectedBasis (localValue, frameValue)
      (placement.borrowedPositions (.inl index))).val = (localValue index).val := by
  exact congrArg
    (fun value : Fin (caller.quantumLayout.wire
      (placement.borrowedPositions (.inl index)).val).dimension => value.val)
    (Equiv.piCongr_apply_apply
      (W := placement.borrowedValueType)
      (Z := fun position : QuantumLayout.SelectedPosition caller.borrowedSelection =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      placement.borrowedPositions placement.borrowedValueEquiv
      ((Equiv.sumPiEquivProdPi placement.borrowedValueType).symm (localValue, frameValue))
      (.inl index))

/-- Complement borrowed values are retained on their unchanged physical wires. -/
lemma contextEmbedding_borrowedSelectedBasis_frame_value
    (localValue : localCtx.quantumLayout.SelectedBasis localCtx.borrowedSelection)
    (frameValue : placement.frame.quantumLayout.SelectedBasis placement.frame.borrowedSelection)
    (index : QuantumLayout.SelectedPosition placement.frame.borrowedSelection) :
    (placement.borrowedSelectedBasis (localValue, frameValue)
      (placement.borrowedPositions (.inr index))).val = (frameValue index).val := by
  exact congrArg
    (fun value : Fin (caller.quantumLayout.wire
      (placement.borrowedPositions (.inr index)).val).dimension => value.val)
    (Equiv.piCongr_apply_apply
      (W := placement.borrowedValueType)
      (Z := fun position : QuantumLayout.SelectedPosition caller.borrowedSelection =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      placement.borrowedPositions placement.borrowedValueEquiv
      ((Equiv.sumPiEquivProdPi placement.borrowedValueType).symm (localValue, frameValue))
      (.inr index))

/-- Borrowed observation and actual full-state reassembly use identical physical coordinates. -/
lemma contextEmbedding_restrictBorrowed_join
    (localValue : localCtx.register.Index) (frameValue : placement.frame.register.Index) :
    caller.quantumLayout.restrictSelectedBasis caller.borrowedSelection
      (placement.basis.symm (localValue, frameValue)) =
        placement.borrowedSelectedBasis
          (localCtx.quantumLayout.restrictSelectedBasis localCtx.borrowedSelection localValue,
            placement.frame.quantumLayout.restrictSelectedBasis
              placement.frame.borrowedSelection frameValue) := by
  funext index
  obtain ⟨original, rfl⟩ := placement.borrowedPositions.surjective index
  apply Fin.ext
  cases original with
  | inl index =>
      exact (placement.contextEmbedding_join_local_value localValue frameValue index.val).trans
        (placement.contextEmbedding_borrowedSelectedBasis_local_value
          (localCtx.quantumLayout.restrictSelectedBasis localCtx.borrowedSelection localValue)
          (placement.frame.quantumLayout.restrictSelectedBasis
            placement.frame.borrowedSelection frameValue) index).symm
  | inr index =>
      exact (placement.contextEmbedding_join_frame_value localValue frameValue index.val).trans
        (placement.contextEmbedding_borrowedSelectedBasis_frame_value
          (localCtx.quantumLayout.restrictSelectedBasis localCtx.borrowedSelection localValue)
          (placement.frame.quantumLayout.restrictSelectedBasis
            placement.frame.borrowedSelection frameValue) index).symm

/-- Reassemble the two complete ordered borrowed registers on the actual caller register. -/
def borrowedBasis :
    localCtx.borrowedQuantumLayout.register.Index ×
      placement.frame.borrowedQuantumLayout.register.Index ≃
        caller.borrowedQuantumLayout.register.Index :=
  (localCtx.borrowedBasisEquiv.symm.prodCongr placement.frame.borrowedBasisEquiv.symm).trans
    (placement.borrowedSelectedBasis.trans caller.borrowedBasisEquiv)

/-- The ordered borrowed observation retains both original sides of the complete caller basis. -/
lemma contextEmbedding_borrowedBasis_join
    (localValue : localCtx.register.Index) (frameValue : placement.frame.register.Index) :
    caller.borrowedBasisEquiv
      (caller.quantumLayout.restrictSelectedBasis caller.borrowedSelection
        (placement.basis.symm (localValue, frameValue))) =
      placement.borrowedBasis
        (localCtx.borrowedBasisEquiv
          (localCtx.quantumLayout.restrictSelectedBasis localCtx.borrowedSelection localValue),
        placement.frame.borrowedBasisEquiv
          (placement.frame.quantumLayout.restrictSelectedBasis
            placement.frame.borrowedSelection frameValue)) := by
  rw [placement.contextEmbedding_restrictBorrowed_join]
  simp only [borrowedBasis, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.symm_apply_apply]

end

end QuantumAlg.ContextEmbedding
