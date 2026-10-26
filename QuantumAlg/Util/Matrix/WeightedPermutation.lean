/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Matrix.Mul

/-!
# Weighted permutation multiplication without expanding matrix entries

Each row has only its actual selected column. Composition therefore
multiplies two scalar weights and composes their original permutations,
without unfolding a finite matrix product into all intermediate indices.
-/

namespace QuantumAlg.WeightedPermutation

variable {Index R : Type*} [DecidableEq Index] [Semiring R]

/-- A weighted row-to-source permutation with its full original coefficient. -/
def matrix (weights : Index → R) (permutation : Equiv.Perm Index) : Matrix Index Index R :=
  fun row column => if permutation row = column then weights row else 0

/-- Multiplication keeps the exact weight and chronological row-to-source composition. -/
lemma mul [Fintype Index] (weights next : Index → R) (first second : Equiv.Perm Index) :
    matrix weights first * matrix next second =
      matrix (fun index => weights index * next (first index)) (first.trans second) := by
  ext row column
  rw [Matrix.mul_apply]
  simp only [matrix]
  rw [Finset.sum_eq_single (first row)]
  · simp [Equiv.trans_apply]
    rfl
  · intro other _ different
    simp [Ne.symm different]
  · simp

/-- Identity permutation keeps the exact diagonal coefficients. -/
lemma refl_eq_diagonal (weights : Index → R) :
    matrix weights (Equiv.refl _) = Matrix.diagonal weights := by
  ext row column
  simp [matrix, Matrix.diagonal_apply]
  rfl

/-- Proving the final permutation is identity exposes the diagonal without expanding its entries. -/
lemma eq_diagonal_of_fixed (weights : Index → R) (permutation : Equiv.Perm Index)
    (fixed : ∀ index, permutation index = index) :
    matrix weights permutation = Matrix.diagonal weights := by
  have same : permutation = Equiv.refl _ := Equiv.ext fixed
  rw [same, refl_eq_diagonal]

end QuantumAlg.WeightedPermutation
