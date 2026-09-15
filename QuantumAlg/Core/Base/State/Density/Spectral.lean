/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density

/-!
# Finite spectral decomposition with the original branch mass

The positive matrix is a finite weighted sum of normalized pure matrices.
The nonnegative weights sum to its actual mass, including mass zero. This
mathematical decomposition introduces no sampling, preparation or normalization
of an execution branch.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

open scoped ComplexOrder

variable {R : Register}

/-- A normalized eigenvector of the same positive finite matrix. -/
def spectralVector (state : DensityOperator R) (index : R.Index) : NormalizedVector R :=
  NormalizedVector.ofVector (state.positive.isHermitian.eigenvectorBasis index)
    (state.positive.isHermitian.eigenvectorBasis.orthonormal.1 index)

/-- The original nonnegative eigenvalue is its pure component's retained mass. -/
def spectralMass (state : DensityOperator R) (index : R.Index) : ℝ :=
  state.positive.isHermitian.eigenvalues index

/-- Every spectral contribution is nonnegative. -/
theorem spectralMass_nonneg (state : DensityOperator R) (index : R.Index) :
    0 ≤ state.spectralMass index := state.positive.eigenvalues_nonneg index

/-- The complete matrix, including all coherences, equals its finite spectral sum. -/
theorem matrix_eq_sum_spectral (state : DensityOperator R) :
    state.matrix = ∑ index, state.spectralMass index •
      (ofPure (state.spectralVector index)).matrix := by
  classical
  conv_lhs =>
    rw [state.positive.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext row column
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply, Matrix.smul_apply,
    ofPure_matrix, spectralVector, NormalizedVector.ofVector, spectralMass,
    Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- The decomposition keeps the actual mass instead of replacing it by one. -/
theorem sum_spectralMass (state : DensityOperator R) :
    ∑ index, state.spectralMass index = state.mass := by
  have traced := congrArg (fun matrix : HilbertOperator R => matrix.trace.re)
    state.matrix_eq_sum_spectral
  have pureMass (input : NormalizedVector R) : (ofPure input).matrix.trace.re = 1 :=
    ofPure_normalized input
  simp only [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.smul_re,
    pureMass, smul_eq_mul, mul_one] at traced
  exact traced.symm

end

end QuantumAlg.DensityOperator
