/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Measurement

/-!
# Named one-qubit kets

The standard one-qubit computational- and Hadamard-basis kets, as named
instances of the generic basis ket `QuantumAlg.PureState.ket`:

`|0⟩, |1⟩, |+⟩ = (|0⟩+|1⟩)/√2, |−⟩ = (|0⟩−|1⟩)/√2`,

together with the ubiquitous normalization scalar `invSqrt2 = (√2)⁻¹` and the
two marginal-probability "workhorse" lemmas for a `|0⟩ ⊗ α + |1⟩ ⊗ β` split.

This is a `Components` module (named instances built on the `Core` framework),
kept out of `Core/State.lean` so the base state type carries no commitment to
particular kets.

Pinned Mathlib API: `Fin.sum_univ_two`, `Real.mul_self_sqrt`,
`Real.sqrt_ne_zero'`.
-/

@[expose] public section

namespace QuantumAlg

namespace PureState

noncomputable section

/-- `|0⟩`, the first one-qubit basis ket. -/
def ket0 : PureState 1 := ket 0

/-- `|1⟩`, the second one-qubit basis ket. -/
def ket1 : PureState 1 := ket 1

/-- `(√2)⁻¹ : ℂ`, the ubiquitous normalization scalar. -/
def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp]
theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

@[simp]
theorem star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2, star_inv₀, Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem norm_invSqrt2 : ‖invSqrt2‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrt2, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2)]

theorem invSqrt2_ne_zero : invSqrt2 ≠ 0 :=
  inv_ne_zero <| Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (by norm_num)

/-- `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
def ketPlus : PureState 1 := invSqrt2 • (ket0 + ket1)

/-- `|−⟩ = (|0⟩ − |1⟩)/√2`. -/
def ketMinus : PureState 1 := invSqrt2 • (ket0 - ket1)

@[simp]
theorem ketPlus_apply (i : Fin (2 ^ 1)) : ketPlus i = invSqrt2 := by
  fin_cases i <;>
    simp [ketPlus, ket0, ket1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]

@[simp]
theorem ketMinus_apply (i : Fin (2 ^ 1)) :
    ketMinus i = if i = 0 then invSqrt2 else -invSqrt2 := by
  fin_cases i <;>
    simp [ketMinus, ket0, ket1, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

private theorem norm_sq_invSqrt2 : ‖invSqrt2‖ ^ 2 = 2⁻¹ := by
  rw [norm_invSqrt2, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Norm over `Fin (2 ^ 1)` as a two-term sum (bridges the `2 ^ 1`-vs-`2`
literal so that `Fin.sum_univ_two`-style reasoning applies). -/
private theorem norm_eq_two_terms (ψ : PureState 1) :
    ‖ψ‖ = √(‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  exact Fin.sum_univ_two (f := fun i : Fin (2 ^ 1) => ‖ψ i‖ ^ 2)

@[simp]
theorem norm_ketPlus : ‖ketPlus‖ = 1 := by
  rw [norm_eq_two_terms, ketPlus_apply, ketPlus_apply, ← two_mul,
    norm_sq_invSqrt2]
  norm_num

@[simp]
theorem norm_ketMinus : ‖ketMinus‖ = 1 := by
  rw [norm_eq_two_terms, ketMinus_apply, ketMinus_apply, if_pos rfl,
    if_neg (show (1 : Fin (2 ^ 1)) ≠ 0 by decide), norm_neg, ← two_mul,
    norm_sq_invSqrt2]
  norm_num

/-- Workhorse for test circuits: on `|0⟩ ⊗ α + |1⟩ ⊗ β` the probability
of reading `0` on qubit 0 is `‖α‖²`. -/
theorem probQubit0_ket0_tensor_add_ket1_tensor {n : ℕ} (α β : PureState n) :
    probQubit0 (ket0.tensor α + ket1.tensor β) 0 = ‖α‖ ^ 2 := by
  rw [probQubit0, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖α i‖)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.add_apply, tensor_apply_prod, tensor_apply_prod, ket0, ket1,
    ket_apply, ket_apply, if_pos rfl,
    if_neg (show (0 : Fin (2 ^ 1)) ≠ 1 by decide), one_mul, zero_mul,
    add_zero]

/-- On `|0⟩ ⊗ α + |1⟩ ⊗ β` the probability of reading `1` on qubit 0 is
`‖β‖²`. -/
theorem probQubit1_ket0_tensor_add_ket1_tensor {n : ℕ} (α β : PureState n) :
    probQubit0 (ket0.tensor α + ket1.tensor β) 1 = ‖β‖ ^ 2 := by
  rw [probQubit0, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖β i‖)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.add_apply, tensor_apply_prod, tensor_apply_prod, ket0, ket1,
    ket_apply, ket_apply, if_pos rfl,
    if_neg (show (1 : Fin (2 ^ 1)) ≠ 0 by decide), one_mul, zero_mul,
    zero_add]

end

end PureState

end QuantumAlg
