/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Execution.State.Marginal

/-!
# Partial trace in explicit subsystem coordinates

Changing only the retained subsystem's basis commutes with observing away an
external reference. Regrouping a tensor product gives the same iterated trace.
Both identities retain every classical block and all retained off-diagonal
entries [dW19, qcnotes.tex:389,5381,6827].
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C : Type} [Fintype C] {R S T : Register}

/-- Relabeling the retained subsystem commutes with tracing the unchanged reference. -/
public lemma executionState_marginalLeft_reindex_local
    (state : ExecutionState C (R.prod T)) (basis : R.Index ≃ S.Index) :
    (state.reindex (S := S.prod T)
        (basis.prodCongr (Equiv.refl T.Index))).marginalLeft =
      state.marginalLeft.reindex (S := S) basis := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [executionState_marginalLeft_entry, reindex_block_entry]
  rfl

/-- A grouped reference trace equals tracing its two factors in succession. -/
public lemma executionState_marginalLeft_reindex_assoc
    (state : ExecutionState C ((R.prod S).prod T)) :
    (state.reindex (S := R.prod (S.prod T))
      (Equiv.prodAssoc R.Index S.Index T.Index)).marginalLeft =
        state.marginalLeft.marginalLeft := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [executionState_marginalLeft_entry, reindex_block_entry]
  change (∑ pair : S.Index × T.Index,
      (state.block value).matrix ((row, pair.1), pair.2) ((column, pair.1), pair.2)) =
    ∑ frame : S.Index, ∑ reference : T.Index,
      (state.block value).matrix ((row, frame), reference) ((column, frame), reference)
  exact Fintype.sum_prod_type _

end

end QuantumAlg.ExecutionState
