/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.Realization

/-!
# First Clifford moment and centered loss

This leaf proves the scalar first-moment formula and its zero-mean consequences
for trace pairings and centered Clifford losses.
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

private lemma qubitClifford_commutant_scalar
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ g, qubitClifford g * M = M * qubitClifford g) :
    ∃ c : ℂ, M = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨M 0 0, ?_⟩
  have hI := hM (.axis false 1)
  have hH := hM (.half fun _ => false)
  have hI01 := congrFun (congrFun hI 0) 1
  have hI10 := congrFun (congrFun hI 1) 0
  have hH01 := congrFun (congrFun hH 0) 1
  simp only [qubitClifford, binaryOctahedralQuaternion, signed] at hI01 hI10
  simp only [realQuaternion] at hI01 hI10
  simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul] at hI01 hI10
  simp only [quaternionMatrix, Bool.false_eq_true, ↓reduceIte, quaternionBasis,
    Fin.isValue, cons_val, smul_eq_mul, mul_zero, sqrtTwoEval_apply,
    QuadraticAlgebra.re_zero, Rat.cast_zero, QuadraticAlgebra.im_zero, zero_mul,
    add_zero, Complex.ofReal_zero, mul_one, QuadraticAlgebra.re_one, Rat.cast_one,
    QuadraticAlgebra.im_one, Complex.ofReal_one, one_mul, zero_add, neg_zero,
    zero_sub, Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one,
    cons_val_zero, Fin.sum_univ_two, cons_val_one, mul_neg, neg_mul] at hI01 hI10
  simp only [qubitClifford, binaryOctahedralQuaternion, halfCoefficient, signed] at hH01
  simp only [realQuaternion] at hH01
  simp only [quaternionMatrix, Bool.false_eq_true, ↓reduceIte, one_div,
    sqrtTwoEval_apply, Rat.cast_inv, Rat.cast_ofNat, Rat.cast_zero, zero_mul,
    add_zero, Complex.ofReal_inv, Complex.ofReal_ofNat, Fin.isValue,
    Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one, cons_val_zero,
    Fin.sum_univ_two, cons_val_one] at hH01
  have hI01' : (2 * Complex.I) * M 0 1 = 0 := by
    have hsum : Complex.I * M 0 1 + M 0 1 * Complex.I = 0 := by
      rw [hI01]
      ring
    rw [← hsum]
    ring
  have e01 : M 0 1 = 0 :=
    (mul_eq_zero.mp hI01').resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hI10' : (2 * Complex.I) * M 1 0 = 0 := by
    have hsum : Complex.I * M 1 0 + M 1 0 * Complex.I = 0 := by
      linear_combination -hI10
    rw [← hsum]
    ring
  have e10 : M 1 0 = 0 :=
    (mul_eq_zero.mp hI10').resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hH01' : (2⁻¹ + 2⁻¹ * Complex.I : ℂ) * M 1 1 =
      M 0 0 * (2⁻¹ + 2⁻¹ * Complex.I : ℂ) := by
    simpa [e01, e10] using hH01
  have hcoef : (2⁻¹ + 2⁻¹ * Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have e11 : M 1 1 = M 0 0 := by
    rw [mul_comm (M 0 0)] at hH01'
    exact mul_left_cancel₀ hcoef hH01'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, e10, e11]

/-- The single-qubit Clifford lift has scalar first moment. -/
lemma qubitClifford_repTwirl_eq_scalar (O : Matrix (Fin 2) (Fin 2) ℂ) :
    repTwirl qubitClifford O = (O.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  repTwirl_eq_scalar qubitClifford qubitClifford_mul qubitClifford_unitary O
    qubitClifford_commutant_scalar

/-- Traceless observables have zero single-qubit Clifford first moment. -/
lemma qubitClifford_repTwirl_eq_zero_of_trace_eq_zero
    (O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    repTwirl qubitClifford O = 0 :=
  repTwirl_eq_zero_of_trace_eq_zero qubitClifford O
    (qubitClifford_repTwirl_eq_scalar O) htr

/-- The scalar Clifford first moment gives zero averaged loss for traceless observables. -/
lemma qubitClifford_loss_mean_eq_zero
    (ρ O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    (ρ * repTwirl qubitClifford O).trace = 0 :=
  repTwirl_trace_pairing_eq_zero_of_trace_eq_zero qubitClifford ρ O
    (qubitClifford_repTwirl_eq_scalar O) htr

/-- The trace pairing of `ρ` with the Clifford conjugate of `O` at the code `g`. -/
public noncomputable def cliffordLoss (ρ O : Matrix (Fin 2) (Fin 2) ℂ)
    (g : BinaryOctahedral) : ℂ :=
  (ρ * (qubitClifford g * O * (qubitClifford g)ᴴ)).trace

lemma cliffordLoss_mean_eq_trace_repTwirl (ρ O : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, cliffordLoss ρ O g =
      (ρ * repTwirl qubitClifford O).trace := by
  unfold cliffordLoss repTwirl
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum, smul_eq_mul]

lemma cliffordLoss_mean_eq_zero_of_trace_eq_zero
    (ρ O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, cliffordLoss ρ O g = 0 := by
  rw [cliffordLoss_mean_eq_trace_repTwirl, qubitClifford_loss_mean_eq_zero ρ O htr]

lemma cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    (ρ O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss ρ O g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ h, cliffordLoss ρ O h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, (cliffordLoss ρ O g) ^ 2 :=
  secondMoment_eq_centered_of_mean_zero (cliffordLoss ρ O)
    (cliffordLoss_mean_eq_zero_of_trace_eq_zero ρ O htr)

end QuantumAlg.QubitTwoDesign

end
