/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# Matrix multiplication restricted to a supported control block

The right factor has no amplitude from the selected input block into any
other control block. Restricting the product therefore preserves the exact
factor order without expanding any circuit or register representation.
-/

namespace QuantumAlg.MatrixSupport

/-- A right factor supported on control zero makes the selected block multiplicative. -/
lemma zeroControl_submatrix_mul {Source Block R : Type*}
    [Fintype Source] [Fintype Block] [Semiring R] (basis : Source ≃ Fin 2 × Block)
    (left right : Matrix Source Source R)
    (zeroRows : ∀ (control : Fin 2) (row column : Block), control ≠ 0 →
      right (basis.symm (control, row)) (basis.symm (0, column)) = 0) :
    (left * right).submatrix (fun row => basis.symm (0, row))
        (fun column => basis.symm (0, column)) =
      left.submatrix (fun row => basis.symm (0, row)) (fun column => basis.symm (0, column)) *
        right.submatrix (fun row => basis.symm (0, row))
          (fun column => basis.symm (0, column)) := by
  ext row column
  change (∑ middle : Source,
    left (basis.symm (0, row)) middle * right middle (basis.symm (0, column))) =
      ∑ middle : Block,
        left (basis.symm (0, row)) (basis.symm (0, middle)) *
          right (basis.symm (0, middle)) (basis.symm (0, column))
  rw [← basis.symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  have nonzeroControl : (∑ middle : Block,
      left (basis.symm (0, row)) (basis.symm (1, middle)) *
        right (basis.symm (1, middle)) (basis.symm (0, column))) = 0 := by
    apply Finset.sum_eq_zero
    intro middle _
    rw [zeroRows 1 middle column (by decide), mul_zero]
  rw [nonzeroControl, add_zero]

end QuantumAlg.MatrixSupport
