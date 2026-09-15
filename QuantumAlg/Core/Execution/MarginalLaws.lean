/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Quantum marginals of fixed unitary steps and constant classical observations

A fixed unitary conjugates the sum of the classical blocks exactly as it
conjugates each block before summation [dW19, qcnotes.tex:5405]. The register
may contain an arbitrary joint input and external reference; taking the
operator to be a local unitary tensored with the reference identity requires
no separability assumption.

A constant classical observation collects every original block once. The
resulting block is the complete quantum marginal, including its original
probability mass. This is a mathematical observation, not a runtime release
or a renormalization of the observed state.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] {R : Register}

/-- Applying the same unitary to every classical block commutes with the finite
sum that defines the full quantum marginal. -/
public theorem executionState_sum_unitaryBlocks (state : ExecutionState C R)
    (operator : UnitaryOperator R) :
    (∑ value : C, (DensityOperator.applyUnitary operator (state.block value)).matrix) =
      (DensityOperator.applyUnitary operator state.quantumMarginal).matrix := by
  change (∑ value : C,
    (operator : HilbertOperator R) * (state.block value).matrix *
      (operator : HilbertOperator R).conjTranspose) =
    (operator : HilbertOperator R) * (∑ value : C, (state.block value).matrix) *
      (operator : HilbertOperator R).conjTranspose
  rw [Matrix.mul_sum, Matrix.sum_mul]

/-- The existing state update with one fixed unitary preserves the same exact
conjugation law after forgetting the classical label. -/
theorem fixedUnitary_quantumMarginal (state : ExecutionState C R)
    (operator : UnitaryOperator R) :
    (state.applyUnitary (fun _ => operator)).quantumMarginal =
      DensityOperator.applyUnitary operator state.quantumMarginal := by
  apply DensityOperator.ext
  exact executionState_sum_unitaryBlocks state operator

/-- Observing one constant classical value sums all source blocks exactly once,
without dividing by a probability or discarding any quantum coherence. -/
public theorem executionState_mapClassical_const_block [DecidableEq D]
    (state : ExecutionState C R) (value : D) :
    (state.mapClassical (fun _ => value)).block value = state.quantumMarginal := by
  apply DensityOperator.ext
  change (∑ input : C, if value = value then (state.block input).matrix else 0) =
    ∑ input : C, (state.block input).matrix
  simp only [if_true]

end

end QuantumAlg.ExecutionState
