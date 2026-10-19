/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Finite matrix isometries for complete conditional density blocks

These are the existing four matrix facts extracted from the terminal comparison proof.
They contain no execution, algorithm, Store projection or probability assumption.
Arbitrary complex entries and independent row and column indices are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace TerminalIsometry

noncomputable section

open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- Injective indicator columns preserve every finite source coordinate. -/
lemma indicatorColumns_gram {Physical Bank : Type}
    [Fintype Physical] (includeBank : Bank → Physical)
    (injective : Function.Injective includeBank) :
    Matrix.conjTranspose (fun row column => if row = includeBank column then (1 : ℂ) else 0) *
        (Matrix.of (fun row column => if row = includeBank column then (1 : ℂ) else 0) :
          Matrix Physical Bank ℂ) = 1 := by
  ext row column
  change (∑ physical : Physical,
    star (if physical = includeBank row then (1 : ℂ) else 0) *
      (if physical = includeBank column then (1 : ℂ) else 0)) =
        (if row = column then (1 : ℂ) else 0)
  simp only [apply_ite (fun value : ℂ => star value), star_one, star_zero, ite_mul,
    one_mul, zero_mul, Fintype.sum_ite_eq', injective.eq_iff]

/-- A bijective change of bank coordinates preserves the complete density sandwich. -/
lemma sandwich_reindex {OldBank NewBank Physical : Type}
    [Fintype OldBank] [Fintype NewBank]
    (coordinates : NewBank ≃ OldBank) (columns : Matrix Physical OldBank ℂ)
    (density : Matrix NewBank NewBank ℂ) :
    columns * density.submatrix coordinates.symm coordinates.symm * columns.conjTranspose =
      columns.submatrix id coordinates * density *
        (columns.submatrix id coordinates).conjTranspose := by
  calc
    _ = (columns * density.submatrix coordinates.symm coordinates.symm *
        columns.conjTranspose).submatrix (Equiv.refl _) (Equiv.refl _) := rfl
    _ = columns.submatrix (Equiv.refl _) coordinates *
        (density.submatrix coordinates.symm coordinates.symm).submatrix coordinates coordinates *
        columns.conjTranspose.submatrix coordinates (Equiv.refl _) := by
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    _ = _ := by
      simp only [Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply,
        Equiv.coe_refl, Matrix.conjTranspose_submatrix]
      rfl

/-- An isometric inclusion recovers the full source matrix by pullback. -/
lemma isometry_pullback {Bank Physical : Type} [Fintype Bank] [Fintype Physical]
    (columns : Matrix Physical Bank ℂ) (gram : columns.conjTranspose * columns = 1)
    (density : Matrix Bank Bank ℂ) :
    columns.conjTranspose * (columns * density * columns.conjTranspose) * columns = density := by
  calc
    _ = (columns.conjTranspose * columns) * density *
        (columns.conjTranspose * columns) := by simp only [Matrix.mul_assoc]
    _ = density := by rw [gram, Matrix.one_mul, Matrix.mul_one]

/-- Two isometric output representations preserve every conditional matrix entry. -/
lemma isometry_transfer {Bank Left Right : Type}
    [Fintype Bank] [Fintype Right]
    (left : Matrix Left Bank ℂ) (right : Matrix Right Bank ℂ)
    (gram : right.conjTranspose * right = 1) (density : Matrix Bank Bank ℂ) :
    (left * right.conjTranspose) * (right * density * right.conjTranspose) *
        (left * right.conjTranspose).conjTranspose =
      left * density * left.conjTranspose := by
  calc
    _ = left * (right.conjTranspose * right) * density *
        (right.conjTranspose * right) * left.conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [gram, Matrix.mul_one, Matrix.mul_one]

end

end TerminalIsometry
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
