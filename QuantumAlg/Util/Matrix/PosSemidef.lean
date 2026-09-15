/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Kernels of finite positive semidefinite matrices

A vector with zero quadratic form lies in the matrix kernel. This follows
from Cauchy-Schwarz for the seminorm induced by that same positive matrix;
no positive definiteness or division by its mass is needed.
-/

open scoped ComplexOrder

namespace Matrix.PosSemidef

noncomputable section

/-- Vanishing quadratic mass forces the complete matrix-vector product to vanish. -/
theorem mulVec_eq_zero_of_quadratic_eq_zero {ι : Type*} [Fintype ι]
    {matrix : Matrix ι ι ℂ} (positive : matrix.PosSemidef) (vector : ι → ℂ)
    (quadratic : star vector ⬝ᵥ (matrix *ᵥ vector) = 0) : matrix *ᵥ vector = 0 := by
  classical
  let inducedGroup := Matrix.toSeminormedAddCommGroup matrix positive
  let inducedInner : @InnerProductSpace ℂ (ι → ℂ) _ inducedGroup :=
    Matrix.toInnerProductSpace matrix positive
  let pairing : (ι → ℂ) → (ι → ℂ) → ℂ := @inner ℂ (ι → ℂ) inducedInner.toInner
  have innerSelf : pairing vector vector = 0 := by
    change (matrix *ᵥ vector) ⬝ᵥ star vector = 0
    rw [dotProduct_comm]
    exact quadratic
  have innerZero (other : ι → ℂ) : pairing other vector = 0 := by
    have bound : ‖pairing other vector‖ * ‖pairing vector other‖ ≤
        (pairing other other).re * (pairing vector vector).re :=
      @inner_mul_inner_self_le ℂ (ι → ℂ) _ inducedGroup inducedInner other vector
    have symmetry : ‖pairing vector other‖ = ‖pairing other vector‖ :=
      @norm_inner_symm ℂ (ι → ℂ) _ inducedGroup inducedInner vector other
    rw [symmetry, innerSelf, Complex.zero_re, mul_zero] at bound
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (pairing other vector)]
  funext index
  change (matrix *ᵥ vector) index = (0 : ℂ)
  have coordinate := innerZero (Pi.single index 1)
  change (matrix *ᵥ vector) ⬝ᵥ star (Pi.single index (1 : ℂ)) = 0 at coordinate
  simpa only [Pi.star_single, star_one, dotProduct_single_one] using coordinate

/-- A zero positive compression annihilates every column of the compressing matrix. -/
theorem mul_eq_zero_of_compression_eq_zero {ι κ : Type*} [Fintype ι]
    {matrix : Matrix ι ι ℂ} (positive : matrix.PosSemidef) (columns : Matrix ι κ ℂ)
    (compression : columns.conjTranspose * matrix * columns = 0) : matrix * columns = 0 := by
  rw [Matrix.mul_assoc] at compression
  ext row column
  have quadratic : star (fun index => columns index column) ⬝ᵥ
      (matrix *ᵥ fun index => columns index column) = 0 :=
    congrArg (fun value : Matrix κ κ ℂ => value column column) compression
  exact congrFun (positive.mulVec_eq_zero_of_quadratic_eq_zero
    (fun index => columns index column) quadratic) row

end

end Matrix.PosSemidef
