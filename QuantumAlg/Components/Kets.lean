/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Marginal

/-!
# Named one-qubit kets

The standard one-qubit computational- and Hadamard-basis kets, as Components-layer
instances of the generic basis ket `QuantumAlg.NormalizedVector.ket`:

`|0>`, `|1>`, `|+> = (|0> + |1>)/sqrt 2`, and
`|-> = (|0> - |1>)/sqrt 2`.

Linear combinations are formed at the raw `HilbertVector` layer and then certified
as metadata-free `NormalizedVector` values once their unit norm has been proved.
-/

section

namespace QuantumAlg

namespace NormalizedVector

noncomputable section

/-- `|0>`, the first one-qubit basis ket. -/
@[expose] public def ket0 : NormalizedVector (Qubits 1) := ket 0

/-- `|1>`, the second one-qubit basis ket. -/
@[expose] public def ket1 : NormalizedVector (Qubits 1) := ket 1

@[simp] public theorem ket0_apply (index : Fin 2) :
    (ket0 : HilbertVector (Qubits 1)) index =
      if index = 0 then 1 else 0 := by
  exact ket_apply (R := Qubits 1) 0 index

/-- `(sqrt 2)^-1 : ℂ`, the ubiquitous normalization scalar. -/
@[expose] public def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp]
public theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

@[simp]
theorem invSqrt2_sq : invSqrt2 ^ 2 = (2 : ℂ)⁻¹ := by
  rw [sq, invSqrt2_mul_self]

@[simp]
theorem invSqrt2_mul_mul_invSqrt2 (z : ℂ) :
    invSqrt2 * (z * invSqrt2) = (2 : ℂ)⁻¹ * z := by
  calc
    invSqrt2 * (z * invSqrt2) = z * (invSqrt2 * invSqrt2) := by ring
    _ = z * (2 : ℂ)⁻¹ := by rw [invSqrt2_mul_self]
    _ = (2 : ℂ)⁻¹ * z := by ring

@[simp]
public theorem star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2, star_inv₀, Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem norm_invSqrt2 : ‖invSqrt2‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrt2, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2)]

theorem invSqrt2_ne_zero : invSqrt2 ≠ 0 :=
  inv_ne_zero <| Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (by norm_num)

theorem norm_sq_invSqrt2 : ‖invSqrt2‖ ^ 2 = 2⁻¹ := by
  rw [norm_invSqrt2, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Norm over `Fin (2 ^ 1)` as a two-term sum. -/
theorem norm_eq_two_terms (ψ : HilbertVector (Qubits 1)) :
    ‖ψ‖ = √(‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  exact Fin.sum_univ_two (f := fun i : Fin (2 ^ 1) => ‖ψ i‖ ^ 2)

/-- `|+> = (|0> + |1>)/sqrt 2`. -/
public def ketPlus : NormalizedVector (Qubits 1) :=
  ofVector
    (invSqrt2 •
      ((ket0 : HilbertVector (Qubits 1)) + (ket1 : HilbertVector (Qubits 1))))
    (by
      rw [norm_eq_two_terms]
      have h0 :
          (invSqrt2 •
            ((ket0 : HilbertVector (Qubits 1)) +
              (ket1 : HilbertVector (Qubits 1)))) 0 = invSqrt2 := by
        simp [ket0, ket1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      have h1 :
          (invSqrt2 •
            ((ket0 : HilbertVector (Qubits 1)) +
              (ket1 : HilbertVector (Qubits 1)))) 1 = invSqrt2 := by
        simp [ket0, ket1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      rw [h0, h1, ← two_mul, norm_sq_invSqrt2]
      norm_num)

/-- `|-> = (|0> - |1>)/sqrt 2`. -/
public def ketMinus : NormalizedVector (Qubits 1) :=
  ofVector
    (invSqrt2 •
      ((ket0 : HilbertVector (Qubits 1)) - (ket1 : HilbertVector (Qubits 1))))
    (by
      rw [norm_eq_two_terms]
      have h0 :
          (invSqrt2 •
            ((ket0 : HilbertVector (Qubits 1)) -
              (ket1 : HilbertVector (Qubits 1)))) 0 = invSqrt2 := by
        simp [ket0, ket1, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have h1 :
          (invSqrt2 •
            ((ket0 : HilbertVector (Qubits 1)) -
              (ket1 : HilbertVector (Qubits 1)))) 1 = -invSqrt2 := by
        simp [ket0, ket1, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [h0, h1, norm_neg, ← two_mul, norm_sq_invSqrt2]
      norm_num)

theorem ketPlus_coe :
    (ketPlus : HilbertVector (Qubits 1)) =
      invSqrt2 •
        ((ket0 : HilbertVector (Qubits 1)) + (ket1 : HilbertVector (Qubits 1))) :=
  rfl

theorem ketMinus_coe :
    (ketMinus : HilbertVector (Qubits 1)) =
      invSqrt2 •
        ((ket0 : HilbertVector (Qubits 1)) - (ket1 : HilbertVector (Qubits 1))) :=
  rfl

@[simp]
public theorem ketPlus_apply (i : Fin (2 ^ 1)) : ketPlus i = invSqrt2 := by
  fin_cases i <;>
    simp [ketPlus, ket0, ket1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]

@[simp]
theorem ketMinus_apply (i : Fin (2 ^ 1)) :
    ketMinus i = if i = 0 then invSqrt2 else -invSqrt2 := by
  fin_cases i <;>
    simp [ketMinus, ket0, ket1, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

theorem norm_ketPlus : ‖ketPlus‖ = 1 := by
  exact ketPlus.norm_eq_one

theorem norm_ketMinus : ‖ketMinus‖ = 1 := by
  exact ketMinus.norm_eq_one

/-- Workhorse for test circuits: the leading-`0` weight of
`|0> ⊗ alpha + |1> ⊗ beta` is `‖alpha‖^2`. -/
theorem leadingQubitWeight_ket0_tensor_add_ket1_tensor {n : ℕ}
    (α β : HilbertVector (Qubits n)) :
    HilbertVector.leadingQubitWeight
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) α
          + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) β) 0
      = ‖α‖ ^ 2 := by
  rw [HilbertVector.leadingQubitWeight, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖α i‖)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.add_apply, HilbertVector.tensor_apply_prod, HilbertVector.tensor_apply_prod,
    ket0, ket1, ket_apply, ket_apply, if_pos rfl,
    if_neg (show (0 : Fin (2 ^ 1)) ≠ 1 by decide), one_mul, zero_mul,
    add_zero]

/-- The leading-`1` weight of `|0> ⊗ alpha + |1> ⊗ beta` is `‖beta‖^2`. -/
theorem leadingQubitWeight_one_ket0_tensor_add_ket1_tensor {n : ℕ}
    (α β : HilbertVector (Qubits n)) :
    HilbertVector.leadingQubitWeight
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) α
          + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) β) 1
      = ‖β‖ ^ 2 := by
  rw [HilbertVector.leadingQubitWeight, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖β i‖)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.add_apply, HilbertVector.tensor_apply_prod, HilbertVector.tensor_apply_prod,
    ket0, ket1, ket_apply, ket_apply, if_pos rfl,
    if_neg (show (1 : Fin (2 ^ 1)) ≠ 0 by decide), one_mul, zero_mul,
    zero_add]

end

end NormalizedVector

end QuantumAlg

end
