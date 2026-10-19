/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Selection.Complement
public import QuantumAlg.Core.Execution.State.Marginal
public import QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Complement
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Execution.Observe

/-!
# Exact selected-state observation through physical placement

The caller selection observes the same original selected local wires. Its
complement trace is exactly the local complement trace followed by the full
frame trace. External-reference row and column indices remain independent,
so the equality retains all selected/reference coherences
[dW19, qcnotes.tex:389,5381,6827].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- Each selected/reference matrix entry sums precisely the unchanged frame diagonal. -/
lemma contextEmbedding_observeSelectionWithReference_entry
    (selected : Finset (Fin localCtx.systemCount)) (Reference : Register)
    (state : DensityOperator (caller.register.prod Reference))
    (row column : localCtx.quantumLayout.SelectedBasis selected)
    (refRow refColumn : Reference.Index) :
    (DensityOperator.observeSelectionWithReference caller.quantumLayout
      (placement.selection selected) Reference state).matrix
        (placement.selectedBasis selected row, refRow)
        (placement.selectedBasis selected column, refColumn) =
      ∑ frame : placement.frame.register.Index,
        (DensityOperator.observeSelectionWithReference localCtx.quantumLayout selected
          (placement.frame.register.prod Reference)
          (state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
            (placement.referenceBasis Reference))).matrix
            (row, (frame, refRow)) (column, (frame, refColumn)) := by
  rw [DensityOperator.observeSelectionWithReference_entry]
  rw [← (placement.complementBasis selected).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [placement.contextEmbedding_joinSelectedBasis]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro frame _
  rw [DensityOperator.observeSelectionWithReference_entry]
  apply Finset.sum_congr rfl
  intro complement _
  rfl

/-- The whole selected/reference density operator obeys the exact physical trace transport. -/
lemma contextEmbedding_observeSelectionWithReference
    (selected : Finset (Fin localCtx.systemCount)) (Reference : Register)
    (state : DensityOperator (caller.register.prod Reference)) :
    (DensityOperator.observeSelectionWithReference caller.quantumLayout
      (placement.selection selected) Reference state).reindex
        (S := (localCtx.quantumLayout.selectedRegister selected).prod Reference)
        ((placement.selectedBasis selected).symm.prodCongr (Equiv.refl Reference.Index)) =
    ((DensityOperator.observeSelectionWithReference localCtx.quantumLayout selected
      (placement.frame.register.prod Reference)
      (state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference))).reindex
          (S := ((localCtx.quantumLayout.selectedRegister selected).prod Reference).prod
            placement.frame.register)
          ExecutionState.referenceFrameBasis).marginalLeft := by
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, refRow⟩
  rcases column with ⟨column, refColumn⟩
  rw [DensityOperator.reindex_entry, DensityOperator.marginalLeft_matrix]
  exact placement.contextEmbedding_observeSelectionWithReference_entry
    selected Reference state row column refRow refColumn

end

end QuantumAlg.ContextEmbedding
