/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

/-!
# Symmetric stochastic matrices

A finite symmetric nonnegative matrix with unit row sums also has unit column sums.
-/

@[expose] public section

namespace Matrix

/-- A symmetric row-stochastic matrix on a finite index type. -/
structure SymmetricStochastic (ι : Type*) [Fintype ι] where
  /-- Real transition weights indexed by source and destination. -/
  mat : Matrix ι ι ℝ
  symmetric : mat.IsSymm
  nonneg : ∀ x y, 0 ≤ mat x y
  rowSum_one : ∀ x, ∑ y, mat x y = 1

namespace SymmetricStochastic

lemma colSum_one {ι : Type*} [Fintype ι] (P : SymmetricStochastic ι) (y : ι) :
    ∑ x, P.mat x y = 1 := by
  calc
    ∑ x, P.mat x y = ∑ x, P.mat y x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simpa [Matrix.IsSymm, Matrix.transpose_apply] using
        congrArg (fun M : Matrix _ _ ℝ => M y x) P.symmetric
    _ = 1 := P.rowSum_one y

end SymmetricStochastic
end Matrix
