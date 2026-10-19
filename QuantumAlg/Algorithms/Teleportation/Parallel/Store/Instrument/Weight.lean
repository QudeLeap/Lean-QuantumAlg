/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.NormNum

/-!
# Real weight of a complete retained teleportation branch

The retained branch has amplitude `2⁻ⁿ` [dW19, qcnotes.tex:804,809]. Its
rectangular matrix sandwich therefore has real weight `4⁻ⁿ`, including
`n = 0`. This calculation requires no input factorization or normalization.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument

noncomputable section

private lemma branchAmplitude_squared (count : Nat) :
    star (((2 : ℂ)⁻¹) ^ count) * ((2 : ℂ)⁻¹) ^ count =
      (((1 / 4 : Real) ^ count : Real) : ℂ) := by
  simp only [star_pow, star_inv₀, star_ofNat, ← mul_pow, Complex.ofReal_pow]
  norm_num

/-- The complete instrument amplitude gives the real weight of every retained joint entry. -/
lemma retained_branch_weight {Output Input : Type} [Fintype Input]
    (count : Nat) (retained : Matrix Output Input ℂ) (original : Matrix Input Input ℂ) :
    ((((2 : ℂ)⁻¹) ^ count) • retained) * original *
        ((((2 : ℂ)⁻¹) ^ count) • retained).conjTranspose =
      ((1 / 4 : Real) ^ count) • (retained * original * retained.conjTranspose) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, branchAmplitude_squared]
  ext row column
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

end

end QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument
