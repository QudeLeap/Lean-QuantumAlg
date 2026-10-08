/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density

/-!
# Complete weighted states after finite randomized quantum selection

The sampled outcome chooses a unitary on the entire quantum register. Its
conditional operator is weighted by the declared classical probability, and
the quantum marginal is the sum of these actual weighted operators. The
register may include any untouched external reference.

These are state laws. An executable selection must additionally supply its
actual granted gate/oracle circuit; these equations grant no quantum operation
or independently chosen resource witness.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
  (state : ExecutionState C R) (transition : C → PMF Outcome)
  (operator : C × Outcome → UnitaryOperator R)

/-- Each selected branch acts on the original complete block with its actual probability. -/
theorem kernelChoice_selected_block_matrix (value : C) (outcome : Outcome) :
    (((kernelChoice state transition).applyUnitary operator).block (value, outcome)).matrix =
      (transition value outcome).toReal •
        ((operator (value, outcome) : HilbertOperator R) * (state.block value).matrix *
          (operator (value, outcome) : HilbertOperator R).conjTranspose) := by
  rw [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix,
    kernelChoice_block_matrix, Matrix.mul_smul, Matrix.smul_mul]

/-- Summing the sampled labels gives the full weighted mixture of the selected unitaries. -/
theorem kernelChoice_selected_mixture_matrix :
    ((kernelChoice state transition).applyUnitary operator).quantumMarginal.matrix =
      ∑ value, ∑ outcome, (transition value outcome).toReal •
        ((operator (value, outcome) : HilbertOperator R) * (state.block value).matrix *
          (operator (value, outcome) : HilbertOperator R).conjTranspose) := by
  change (∑ entry : C × Outcome,
    (((kernelChoice state transition).applyUnitary operator).block entry).matrix) = _
  rw [Fintype.sum_prod_type]
  simp only [kernelChoice_selected_block_matrix]

end

end QuantumAlg.Execution
