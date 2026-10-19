/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Complement
import all QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Complement
import all QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Basis
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Reconstructing the complete borrowed quantum-reference observation

The local borrowed observation keeps the entire quantum complement alongside
the original reference. Only the complement's nonborrowed wires are then
traced, and the remaining borrowed wires are put in their actual caller
positions. The equality preserves every joint off-diagonal matrix entry
[dW19, qcnotes.tex:389,5381,6827].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

private def borrowedFrameBasis (Reference : Register) :
    (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference)).Index ≃
      (placement.frame.register.prod (localCtx.borrowedQuantumLayout.register.prod Reference)).Index
    where
  toFun value := (value.2.1, (value.1, value.2.2))
  invFun value := (value.2.1, (value.1, value.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def borrowedReferenceBasis (Reference : Register) :
    (placement.frame.borrowedQuantumLayout.register.prod
      (localCtx.borrowedQuantumLayout.register.prod Reference)).Index ≃
        (caller.borrowedQuantumLayout.register.prod Reference).Index :=
  (Equiv.prodAssoc placement.frame.borrowedQuantumLayout.register.Index
      localCtx.borrowedQuantumLayout.register.Index Reference.Index).symm.trans
    (((Equiv.prodComm placement.frame.borrowedQuantumLayout.register.Index
      localCtx.borrowedQuantumLayout.register.Index).prodCongr (Equiv.refl Reference.Index)).trans
        (placement.borrowedBasis.prodCongr (Equiv.refl Reference.Index)))

/-- Retain all borrowed wires on both sides, tracing only nonborrowed complement systems. -/
def reassembleBorrowedDensity (Reference : Register)
    (state : DensityOperator
      (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference))) :
    DensityOperator (caller.borrowedQuantumLayout.register.prod Reference) :=
  (placement.frame.observeBorrowedWithReference
    (localCtx.borrowedQuantumLayout.register.prod Reference)
    (state.reindex (S := placement.frame.register.prod
      (localCtx.borrowedQuantumLayout.register.prod Reference))
      (placement.borrowedFrameBasis Reference))).reindex
        (placement.borrowedReferenceBasis Reference)

/-- Reconstructing the complete borrowed observation retains its full branch mass. -/
lemma contextEmbedding_reassembleBorrowedDensity_mass (Reference : Register)
    (state : DensityOperator
      (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference))) :
    (placement.reassembleBorrowedDensity Reference state).mass = state.mass := by
  rw [reassembleBorrowedDensity, DensityOperator.reindex_mass,
    RuntimeCtx.observeBorrowedWithReference_mass, DensityOperator.reindex_mass]

/-- Only nonborrowed complement coordinates are summed when reconstructing one joint entry. -/
lemma contextEmbedding_reassembleBorrowedDensity_entry (Reference : Register)
    (state : DensityOperator
      (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference)))
    (localRow localColumn : localCtx.borrowedQuantumLayout.Basis)
    (frameRow frameColumn : placement.frame.borrowedQuantumLayout.Basis)
    (refRow refColumn : Reference.Index) :
    (placement.reassembleBorrowedDensity Reference state).matrix
      (placement.borrowedBasis (localRow, frameRow), refRow)
      (placement.borrowedBasis (localColumn, frameColumn), refColumn) =
    ∑ frameComplement :
        placement.frame.quantumLayout.ComplementBasis placement.frame.borrowedSelection,
      state.matrix
        (localRow, (placement.frame.quantumLayout.joinSelectedBasis
          placement.frame.borrowedSelection
          (placement.frame.borrowedBasisEquiv.symm frameRow) frameComplement, refRow))
        (localColumn,
          (placement.frame.quantumLayout.joinSelectedBasis placement.frame.borrowedSelection
            (placement.frame.borrowedBasisEquiv.symm frameColumn) frameComplement, refColumn)) := by
  rw [reassembleBorrowedDensity, DensityOperator.reindex_entry]
  change (placement.frame.observeBorrowedWithReference
    (localCtx.borrowedQuantumLayout.register.prod Reference)
    (state.reindex (placement.borrowedFrameBasis Reference))).matrix
      ((placement.borrowedBasis.symm (placement.borrowedBasis (localRow, frameRow))).2,
        ((placement.borrowedBasis.symm (placement.borrowedBasis (localRow, frameRow))).1, refRow))
      ((placement.borrowedBasis.symm (placement.borrowedBasis (localColumn, frameColumn))).2,
        ((placement.borrowedBasis.symm
          (placement.borrowedBasis (localColumn, frameColumn))).1, refColumn)) = _
  simp only [Equiv.symm_apply_apply]
  rw [RuntimeCtx.observeBorrowedWithReference_entry]
  rfl

private lemma borrowedBasis_selected
    (localValue : localCtx.borrowedQuantumLayout.Basis)
    (frameValue : placement.frame.borrowedQuantumLayout.Basis) :
    caller.borrowedBasisEquiv.symm (placement.borrowedBasis (localValue, frameValue)) =
      placement.borrowedSelectedBasis
        (localCtx.borrowedBasisEquiv.symm localValue,
          placement.frame.borrowedBasisEquiv.symm frameValue) := by
  simp only [borrowedBasis, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.symm_apply_apply]

/-- The complete caller borrowed density is recovered from the local observation with full frame. -/
lemma contextEmbedding_observeBorrowedWithReference (Reference : Register)
    (state : DensityOperator (caller.register.prod Reference)) :
    caller.observeBorrowedWithReference Reference state =
      placement.reassembleBorrowedDensity Reference
        (localCtx.observeBorrowedWithReference (placement.frame.register.prod Reference)
          (state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
            (placement.referenceBasis Reference))) := by
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, refRow⟩
  rcases column with ⟨column, refColumn⟩
  obtain ⟨⟨localRow, frameRow⟩, rfl⟩ := placement.borrowedBasis.surjective row
  obtain ⟨⟨localColumn, frameColumn⟩, rfl⟩ := placement.borrowedBasis.surjective column
  rw [RuntimeCtx.observeBorrowedWithReference_entry,
    placement.borrowedBasis_selected, placement.borrowedBasis_selected]
  rw [← placement.borrowedComplementBasis.sum_comp, Fintype.sum_prod_type]
  simp only [placement.contextEmbedding_joinBorrowedSelectedBasis]
  rw [Finset.sum_comm, placement.contextEmbedding_reassembleBorrowedDensity_entry]
  apply Finset.sum_congr rfl
  intro frameComplement _
  rw [RuntimeCtx.observeBorrowedWithReference_entry]
  apply Finset.sum_congr rfl
  intro localComplement _
  rfl

end

end QuantumAlg.ContextEmbedding
