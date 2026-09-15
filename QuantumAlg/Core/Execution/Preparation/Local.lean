/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.State.Density

/-!
# Actual local entries after fresh preparation

Tracing the external reference in the real preparation equation leaves the
prepared pure factor beside the original local density. The joined basis is
the interpreter's physical allocation map, not an arbitrary equal-size
identification [dW19, qcnotes.tex:5381,6827].
-/

namespace QuantumAlg.Circuit

noncomputable section

/-- Local preparation tensors the fresh amplitudes with the actual incoming local entries. -/
theorem prepare_local_joined_entry {ctx : RuntimeCtx .quantum} {Reference : Register}
    {H : Type} [Fintype H] (state : Execution.State ctx Reference H)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout)
    (newRow newColumn : layout.register.Index) (oldRow oldColumn : ctx.register.Index) :
    (((Circuit.prepare ctx key layout fresh disjoint preparation).execute
      Reference state).quantumMarginal.marginalLeft).matrix
        (Execution.preparedLocalBasisEquiv ctx key layout fresh disjoint (newRow, oldRow))
        (Execution.preparedLocalBasisEquiv ctx key layout fresh disjoint (newColumn, oldColumn)) =
      (preparation.normalized newRow * star (preparation.normalized newColumn)) *
        state.quantumMarginal.marginalLeft.matrix oldRow oldColumn := by
  rw [DensityOperator.marginalLeft_matrix]
  calc
    _ = ∑ reference : Reference.Index,
        (preparation.normalized newRow * star (preparation.normalized newColumn)) *
          state.quantumMarginal.matrix (oldRow, reference) (oldColumn, reference) := by
      apply Finset.sum_congr rfl
      intro reference _
      exact prepare_joined_entry state key layout fresh disjoint preparation
        newRow newColumn (oldRow, reference) (oldColumn, reference)
    _ = _ := by
      rw [← Finset.mul_sum]
      exact congrArg (fun value : ℂ =>
        (preparation.normalized newRow * star (preparation.normalized newColumn)) * value)
        (DensityOperator.marginalLeft_matrix state.quantumMarginal oldRow oldColumn).symm

end

end QuantumAlg.Circuit
