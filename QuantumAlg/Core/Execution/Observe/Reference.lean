/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Observe
public import QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.State.Marginal

/-!
# Selected observation and an external reference partial trace

The unselected local wires and an untouched reference factor are disjoint
coordinates of the same density operator. Summing their diagonals in either
order preserves all remaining selected/reference matrix entries
[dW19, qcnotes.tex:5381,6827].
-/

namespace QuantumAlg.DensityOperator

noncomputable section

/-- A basis change of the retained systems commutes with tracing the untouched reference. -/
lemma marginalLeft_reindex_local {R S Reference : Register}
    (state : DensityOperator (R.prod Reference)) (basis : R.Index ≃ S.Index) :
    (state.reindex (S := S.prod Reference)
      (basis.prodCongr (Equiv.refl Reference.Index))).marginalLeft =
        state.marginalLeft.reindex basis := by
  apply DensityOperator.ext
  ext row column
  rw [marginalLeft_matrix, reindex_entry, marginalLeft_matrix]
  rfl

/-- Local selection and tracing an external frame commute on the entire density operator. -/
lemma observeSelectionWithReference_forgetReferenceFrame
    {systemCount : Nat} (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Frame Reference : Register)
    (state : DensityOperator (layout.register.prod (Frame.prod Reference))) :
    observeSelectionWithReference layout selection Reference
      ((state.reindex (S := (layout.register.prod Reference).prod Frame)
        ExecutionState.referenceFrameBasis).marginalLeft) =
    ((observeSelectionWithReference layout selection (Frame.prod Reference) state).reindex
      (S := ((layout.selectedRegister selection).prod Reference).prod Frame)
      ExecutionState.referenceFrameBasis).marginalLeft := by
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, refRow⟩
  rcases column with ⟨column, refColumn⟩
  simp only [observeSelectionWithReference_entry, marginalLeft_matrix, reindex_entry,
    ExecutionState.referenceFrameBasis, Equiv.coe_fn_symm_mk]
  exact Finset.sum_comm

end

end QuantumAlg.DensityOperator
