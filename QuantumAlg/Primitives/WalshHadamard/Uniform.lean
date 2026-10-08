/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Components.Kets
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform phase-register state

The normalized uniform vector and its scalar normalization are mathematical
inputs to Walsh-Hadamard and phase-estimation analysis. They allocate no
runtime storage and do not provide a free preparation instruction.
-/

namespace QuantumAlg.WalshHadamard

noncomputable section

variable {n : Nat}

/-- `(√(2^n))⁻¹`, the normalization scalar of the `n`-qubit Hadamard layer. -/
public def invSqrtCard (n : ℕ) : ℂ := (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹

@[simp]
public theorem star_invSqrtCard (n : ℕ) : star (invSqrtCard n) = invSqrtCard n := by
  rw [invSqrtCard, star_inv₀, Complex.star_def, Complex.conj_ofReal]

@[simp]
public theorem norm_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ = (Real.sqrt ((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [invSqrtCard, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

public theorem norm_sq_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ ^ 2 = (((2 ^ n : ℕ) : ℝ)⁻¹) := by
  rw [norm_invSqrtCard, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]

/-- The uniform normalized vector produced by the first Hadamard layer. -/
public def uniformState (n : ℕ) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun _ => invSqrtCard n)
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ _i : Fin (2 ^ n), ‖invSqrtCard n‖ ^ 2 = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, norm_sq_invSqrtCard]
        norm_num
      rw [hsum, Real.sqrt_one])

private theorem uniformState_apply_internal (x : Fin (2 ^ n)) :
    uniformState n x = invSqrtCard n :=
  rfl

@[simp]
public theorem uniformState_apply (x : Fin (2 ^ n)) : uniformState n x = invSqrtCard n :=
  uniformState_apply_internal x

end

end QuantumAlg.WalshHadamard
