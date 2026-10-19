/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Actual uniform choices preserve source-weighted reference observations

The real finite random instruction scales each original classical quantum
block by the reciprocal of its declared cardinality. A weighted observation
therefore sums over those actual outcomes while retaining each original
block and both external reference coordinates. The weight may depend on the
original classical value, the draw and the local basis coordinate.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- Each actual uniform draw contributes its equal fraction of every full reference entry. -/
lemma referenceFiberSum_uniformChoice {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference)) (count : ℕ+)
    (weight : (C × Fin count) → R.Index → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum (uniformChoice state count) weight leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun value basis => ∑ draw : Fin count,
          (((count : ℝ)⁻¹ : ℝ) : ℂ) * weight (value, draw) basis) leftRef rightRef := by
  unfold ExecutionState.referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro value _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro draw _
  rw [uniformChoice_block_matrix, Matrix.smul_apply, Complex.real_smul]
  ring

end

end QuantumAlg.Execution
