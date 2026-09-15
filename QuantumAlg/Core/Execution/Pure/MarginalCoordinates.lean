/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density.PureMarginal
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Pure-marginal support in explicit basis coordinates

The pure-marginal factorization is unchanged by an explicit basis relabeling.
The right factor remains the actual reference marginal of the original
joint density. No normalized vector or additional payload is reconstructed.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

/-- A pure local promise in explicit coordinates forces the same complete joint factorization. -/
theorem pureMarginal_reindexed_entry {R S Reference : Register}
    (state : DensityOperator (Register.prod R Reference)) (basisEquiv : R.Index ≃ S.Index)
    (pure : NormalizedVector S)
    (promised : state.marginalLeft = (ofPure pure).reindex (S := R) basisEquiv.symm)
    (row column : R.Index) (refRow refColumn : Reference.Index) :
    state.matrix (row, refRow) (column, refColumn) =
      (pure (basisEquiv row) * star (pure (basisEquiv column))) *
        ∑ index : R.Index, state.matrix (index, refRow) (index, refColumn) := by
  let encoded : DensityOperator (Register.prod S Reference) :=
    state.reindex (S := Register.prod S Reference)
      (basisEquiv.prodCongr (Equiv.refl Reference.Index))
  have encodedPure : encoded.marginalLeft = ofPure pure := by
    dsimp only [encoded]
    rw [reindex_prod_marginalLeft, promised]
    apply DensityOperator.ext
    ext left right
    rw [reindex_entry, reindex_entry]
    simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
  have reference :
      (∑ index : S.Index, encoded.matrix (index, refRow) (index, refColumn)) =
        ∑ index : R.Index, state.matrix (index, refRow) (index, refColumn) := by
    change (∑ index : S.Index,
      state.matrix (basisEquiv.symm index, refRow) (basisEquiv.symm index, refColumn)) = _
    exact basisEquiv.symm.sum_comp
      (fun index => state.matrix (index, refRow) (index, refColumn))
  calc
    _ = encoded.matrix (basisEquiv row, refRow) (basisEquiv column, refColumn) := by
      change state.matrix (row, refRow) (column, refColumn) =
        state.matrix (basisEquiv.symm (basisEquiv row), refRow)
          (basisEquiv.symm (basisEquiv column), refColumn)
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    _ = _ := (pureMarginal_entry encoded pure encodedPure
      (basisEquiv row) (basisEquiv column) refRow refColumn).trans
        (congrArg (fun value : ℂ =>
          (pure (basisEquiv row) * star (pure (basisEquiv column))) * value) reference)

end

end QuantumAlg.DensityOperator
