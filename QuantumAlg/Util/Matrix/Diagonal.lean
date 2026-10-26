/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Matrix.Mul

/-!
# Diagonal matrix multiplication before entry expansion

Keeping the result wrapped in `Matrix.of` lets subsequent matrix rewrites retain
their matrix type, including when a product appears below a submatrix operation.
-/

namespace QuantumAlg

private lemma diagonal_mul_matrix {m n R : Type*} [Fintype m] [DecidableEq m]
    [Semiring R] (d : m → R) (M : Matrix m n R) :
    Matrix.diagonal d * M = Matrix.of (fun i j => d i * M i j) := by
  funext i j
  exact Matrix.diagonal_mul d M i j

end QuantumAlg
