/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.MarginalSum
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Complete stored matrix formulas from their supported columns

Once an actual interpreter's stored blocks have been identified, equality
of operator columns on the input density support extends to their full
joint matrix. Summing the actual stores then yields the independent target
matrix. These are finite-matrix proof rules: they define no circuit,
measurement instruction, probability sampler, or resource witness
[dW19, qcnotes.tex:5381,5394,5405,6827].
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem scaled_conjugation {R : Register} (state : DensityOperator R)
    (target : HilbertOperator R) (phase : ℂ) :
    (phase • target) * state.matrix * (phase • target).conjTranspose =
      (phase * star phase) • (target * state.matrix * target.conjTranspose) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, mul_comm (star phase) phase]

/-- Exact supported columns and the actual stored-block formulas give the full joint target. -/
theorem full_matrix_of_stored_columns {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (input : DensityOperator (Register.prod ctx.register Reference))
    (result : State ctx Reference History)
    (admissible : (Register.prod ctx.register Reference).Index → Prop)
    (target : HilbertOperator (Register.prod ctx.register Reference))
    (operator : Store ctx → HilbertOperator (Register.prod ctx.register Reference))
    (phase : ℂ)
    (normalized : (Fintype.card (Store ctx) : ℂ) * (phase * star phase) = 1)
    (support : ∀ basis, ¬admissible basis → input.matrix basis basis = 0)
    (columns : ∀ stored basis, admissible basis → ∀ row,
      operator stored row basis = phase * target row basis)
    (actual : ∀ stored,
      (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
        operator stored * input.matrix * (operator stored).conjTranspose) :
    result.quantumMarginal.matrix = target * input.matrix * target.conjTranspose := by
  apply matrix_of_uniform_store_blocks result _ (phase * star phase) normalized
  intro stored
  refine (actual stored).trans ?_
  refine (DensityOperator.conjugation_eq_on_basis_support input admissible
    (operator stored) (phase • target) support ?_).trans (scaled_conjugation input target phase)
  intro basis allowed row
  exact columns stored basis allowed row

end

end QuantumAlg.Execution
