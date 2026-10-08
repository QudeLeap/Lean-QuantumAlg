/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
public import QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# One fixed pure basis marginal in every complete classical block

Positivity forbids an individual block from having support outside the
pure marginal of their sum. Every block therefore retains the same fixed
basis label at its actual mass, including blocks of mass zero. Arbitrary
classical correlations and external references are kept [dW19, qcnotes.tex:5394].
-/

namespace QuantumAlg.ExecutionState

noncomputable section

open scoped ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

/-- A fixed pure local marginal holds separately on every complete classical block. -/
public theorem block_pureKet_of_localMarginal {C : Type} [Fintype C]
    {R Reference : Register} (state : ExecutionState C (R.prod Reference)) (seed : R.Index)
    (promised : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      state.quantumMarginal.marginalLeft) (entry : C) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds (state.block entry).marginalLeft := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  have localZero : state.quantumMarginal.marginalLeft.matrix row row = 0 := by
    change state.quantumMarginal.marginalLeft.matrix =
      state.quantumMarginal.marginalLeft.mass •
        (DensityOperator.ofPure (NormalizedVector.ket seed)).matrix at promised
    rw [promised, Matrix.smul_apply, DensityOperator.ofPure_matrix]
    simp only [NormalizedVector.ket_apply, if_neg different, zero_mul, smul_zero]
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  have jointZero := DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
    state.quantumMarginal row localZero reference
  simp only [ExecutionState.quantumMarginal, Matrix.sum_apply] at jointZero
  change (∑ current : C, (state.block current).matrix (row, reference) (row, reference)) = 0
    at jointZero
  have bound : (state.block entry).matrix (row, reference) (row, reference) ≤
      ∑ current : C, (state.block current).matrix (row, reference) (row, reference) :=
    Finset.single_le_sum (fun current _ =>
      (state.block current).positive.diag_nonneg) (Finset.mem_univ entry)
  have diagonal : (state.block entry).matrix (row, reference) (row, reference) = 0 :=
    le_antisymm (bound.trans_eq jointZero) (state.block entry).positive.diag_nonneg
  exact DensityOperator.row_zero_of_diagonal_zero (state.block entry) (row, reference)
    diagonal (column, reference)

end

end QuantumAlg.ExecutionState
