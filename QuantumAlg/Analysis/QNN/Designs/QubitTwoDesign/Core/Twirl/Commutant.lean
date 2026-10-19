/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.Realization

/-!
# Doubled Clifford commutant

This leaf identifies the doubled single-qubit Clifford commutant and packages
the bridge to the Lie-algebra doubled commutant used by the QNN interface.
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- The tensor-factor swap on two qubits. -/
def qubitSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q =>
  if p = (q.2, q.1) then 1 else 0

lemma kronecker_self_commute_qubitSwap (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (U ⊗ₖ U) * qubitSwap = qubitSwap * (U ⊗ₖ U) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, qubitSwap]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [mul_comm] <;> ring

lemma su2_casimir_eq_swap_sub :
    su2HermBasis.casimir = qubitSwap - (1 / 2 : ℂ) • 1 := by
  rw [DLAHermBasis.casimir]
  change (∑ j : Fin 3, su2B j ⊗ₖ su2B j) = qubitSwap - (1 / 2 : ℂ) • 1
  rw [Fin.sum_univ_three]
  have hrt : rt2inv ^ 2 = (1 / 2 : ℂ) := by simpa [pow_two] using rt2inv_mul_self
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [su2B, pauliX, pauliY, pauliZ, qubitSwap,
      Matrix.smul_apply, rt2inv_mul_self] <;> ring_nf <;>
      simp [hrt, Complex.I_sq] <;> norm_num

/-- The strict Clifford lift fixes the normalized `su(2)` Casimir pointwise. -/
lemma qubitClifford_casimir_commute (g : BinaryOctahedral) :
    (qubitClifford g ⊗ₖ qubitClifford g) * su2HermBasis.casimir =
      su2HermBasis.casimir * (qubitClifford g ⊗ₖ qubitClifford g) := by
  rw [su2_casimir_eq_swap_sub, Matrix.mul_sub, Matrix.sub_mul,
    kronecker_self_commute_qubitSwap]
  simp

/-- A finite unitary ensemble is doubled-commutant complete for `b` if every doubled-operator
commuting with the finite doubled action already lies in the Lie-algebra doubled commutant used by
the Ragone second-moment interface. This is the `2`-design property in the form consumed here. -/
def IsDoubledCommutantComplete {N : ℕ} {G : Type*}
    (u : G → Matrix (Fin N) (Fin N) ℂ)
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens) : Prop :=
  ∀ M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
    (∀ g, (u g ⊗ₖ u g) * M = M * (u g ⊗ₖ u g)) → M ∈ adCommutantGG b

namespace TwirlInternal

/-- Internal normal form shared by the commutant bridge and the concrete basis twirl. -/
lemma qubitClifford_commutant_normal_form
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : ∀ g, (qubitClifford g ⊗ₖ qubitClifford g) * M =
      M * (qubitClifford g ⊗ₖ qubitClifford g)) :
    M = M (1, 0) (1, 0) • 1 +
      (M (0, 0) (0, 0) - M (1, 0) (1, 0)) • qubitSwap := by
  have hI := hM (.axis false 1)
  have hJ := hM (.axis false 2)
  have hH := hM (.half fun _ => false)
  have hI01 := congrFun (congrFun hI (0, 0)) (0, 1)
  have hI02 := congrFun (congrFun hI (0, 0)) (1, 0)
  have hI10 := congrFun (congrFun hI (0, 1)) (0, 0)
  have hI13 := congrFun (congrFun hI (0, 1)) (1, 1)
  have hI20 := congrFun (congrFun hI (1, 0)) (0, 0)
  have hI23 := congrFun (congrFun hI (1, 0)) (1, 1)
  have hI31 := congrFun (congrFun hI (1, 1)) (0, 1)
  have hI32 := congrFun (congrFun hI (1, 1)) (1, 0)
  have hJ03 := congrFun (congrFun hJ (0, 0)) (1, 1)
  have hJ00 := congrFun (congrFun hJ (0, 0)) (0, 0)
  have hJ11 := congrFun (congrFun hJ (0, 1)) (0, 1)
  have hJ12 := congrFun (congrFun hJ (0, 1)) (1, 0)
  have hH00 := congrFun (congrFun hH (0, 0)) (0, 0)
  have hH01 := congrFun (congrFun hH (0, 0)) (0, 1)
  simp only [qubitClifford, binaryOctahedralQuaternion, signed] at hI01 hI02 hI10 hI13
  simp only [qubitClifford, binaryOctahedralQuaternion, signed] at hI20 hI23 hI31 hI32
  simp only [qubitClifford, binaryOctahedralQuaternion, signed] at hJ03 hJ00 hJ11 hJ12
  simp only [realQuaternion] at hI01 hI02 hI10 hI13
  simp only [realQuaternion] at hI20 hI23 hI31 hI32
  simp only [realQuaternion] at hJ03 hJ00 hJ11 hJ12
  simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul] at hI01 hI02 hI10 hI13
  simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul] at hI20 hI23 hI31 hI32
  simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul] at hJ03 hJ00 hJ11 hJ12
  simp only [quaternionMatrix, Bool.false_eq_true, ↓reduceIte, quaternionBasis,
    Fin.isValue, cons_val, smul_eq_mul, mul_zero, sqrtTwoEval_apply,
    QuadraticAlgebra.re_zero, Rat.cast_zero, QuadraticAlgebra.im_zero, zero_mul,
    add_zero, Complex.ofReal_zero, mul_one, QuadraticAlgebra.re_one, Rat.cast_one,
    QuadraticAlgebra.im_one, Complex.ofReal_one, one_mul, zero_add, neg_zero,
    zero_sub, Matrix.mul_apply, kroneckerMap_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, Fintype.sum_prod_type, Fin.sum_univ_two,
    cons_val_one, Complex.I_mul_I, neg_mul, mul_neg, Finset.sum_neg_distrib,
    neg_neg] at hI01 hI02 hI10 hI13
  simp only [quaternionMatrix, Bool.false_eq_true, ↓reduceIte, quaternionBasis,
    Fin.isValue, cons_val, smul_eq_mul, mul_zero, sqrtTwoEval_apply,
    QuadraticAlgebra.re_zero, Rat.cast_zero, QuadraticAlgebra.im_zero, zero_mul,
    add_zero, Complex.ofReal_zero, mul_one, QuadraticAlgebra.re_one, Rat.cast_one,
    QuadraticAlgebra.im_one, Complex.ofReal_one, one_mul, zero_add, neg_zero,
    zero_sub, Matrix.mul_apply, kroneckerMap_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_one, cons_val_zero, Fintype.sum_prod_type,
    Fin.sum_univ_two, neg_mul, Complex.I_mul_I, neg_neg, mul_neg,
    Finset.sum_neg_distrib] at hI20 hI23 hI31 hI32
  simp only [quaternionMatrix, Bool.false_eq_true, ↓reduceIte, quaternionBasis,
    Fin.isValue, cons_val, smul_eq_mul, mul_zero, sqrtTwoEval_apply,
    QuadraticAlgebra.re_zero, Rat.cast_zero, QuadraticAlgebra.im_zero, zero_mul,
    add_zero, Complex.ofReal_zero, mul_one, QuadraticAlgebra.re_one, Rat.cast_one,
    QuadraticAlgebra.im_one, Complex.ofReal_one, sub_self, Matrix.mul_apply,
    kroneckerMap_apply, of_apply, cons_val', cons_val_fin_one, cons_val_zero,
    Fintype.sum_prod_type, Fin.sum_univ_two, cons_val_one, zero_add, one_mul,
    mul_neg, Finset.sum_neg_distrib, neg_neg, neg_mul, neg_inj] at hJ03 hJ00 hJ11 hJ12
  simp only [qubitClifford, binaryOctahedralQuaternion, halfCoefficient, signed] at hH00 hH01
  simp only [realQuaternion] at hH00 hH01
  simp only [quaternionMatrix, Bool.false_eq_true, ↓reduceIte, one_div,
    sqrtTwoEval_apply, Rat.cast_inv, Rat.cast_ofNat, Rat.cast_zero, zero_mul,
    add_zero, Complex.ofReal_inv, Complex.ofReal_ofNat, Fin.isValue,
    Matrix.mul_apply, kroneckerMap_apply, of_apply, cons_val', cons_val_fin_one,
    cons_val_zero, Fintype.sum_prod_type, Fin.sum_univ_two, cons_val_one] at hH00 hH01
  have e01 : M (0, 0) (0, 1) = 0 := by linear_combination (-1 / 2 : ℂ) * hI01
  have e02 : M (0, 0) (1, 0) = 0 := by linear_combination (-1 / 2 : ℂ) * hI02
  have e10 : M (0, 1) (0, 0) = 0 := by linear_combination (1 / 2 : ℂ) * hI10
  have e13 : M (0, 1) (1, 1) = 0 := by linear_combination (1 / 2 : ℂ) * hI13
  have e20 : M (1, 0) (0, 0) = 0 := by linear_combination (1 / 2 : ℂ) * hI20
  have e23 : M (1, 0) (1, 1) = 0 := by linear_combination (1 / 2 : ℂ) * hI23
  have e31 : M (1, 1) (0, 1) = 0 := by linear_combination (-1 / 2 : ℂ) * hI31
  have e32 : M (1, 1) (1, 0) = 0 := by linear_combination (-1 / 2 : ℂ) * hI32
  have e0033 : M (0, 0) (0, 0) = M (1, 1) (1, 1) := by
    linear_combination -hJ03
  have e0312 : M (0, 0) (1, 1) = M (1, 1) (0, 0) := by
    linear_combination -hJ00
  have e1221 : M (0, 1) (1, 0) = M (1, 0) (0, 1) := by
    linear_combination -hJ11
  have e1122 : M (0, 1) (0, 1) = M (1, 0) (1, 0) := by
    linear_combination -hJ12
  simp [e01, e02, e10, e20, e0312] at hH00
  ring_nf at hH00
  simp [Complex.I_sq] at hH00
  have e30 : M (1, 1) (0, 0) = 0 := hH00.resolve_left (by norm_num)
  have e03 : M (0, 0) (1, 1) = 0 := e0312.trans e30
  simp [e01, e02, e03, e31, e1122] at hH01
  ring_nf at hH01
  rw [Complex.I_sq] at hH01
  have e12 : M (0, 1) (1, 0) =
      M (0, 0) (0, 0) - M (0, 1) (0, 1) := by
    linear_combination (-2 * Complex.I) * hH01 + e1221 + e1122 +
      (-M (0, 0) (0, 0) + M (1, 0) (0, 1) + M (1, 0) (1, 0)) * Complex.I_sq
  have e21 : M (1, 0) (0, 1) =
      M (0, 0) (0, 0) - M (0, 1) (0, 1) := e1221.symm.trans e12
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [qubitSwap, e01, e02, e03, e10, e12, e13, e20, e21, e23, e30, e31, e32,
      e0033, e1122]

end TwirlInternal

lemma one_mem_su2_adCommutantGG :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∈ adCommutantGG su2HermBasis := by
  rw [adCommutantGG, Submodule.mem_iInf]
  intro j
  rw [LinearMap.mem_ker]
  simp [doubledAd]

lemma qubitSwap_mem_su2_adCommutantGG : qubitSwap ∈ adCommutantGG su2HermBasis := by
  have hswap : qubitSwap = su2HermBasis.casimir + (1 / 2 : ℂ) • 1 := by
    rw [su2_casimir_eq_swap_sub]
    module
  rw [hswap]
  exact (adCommutantGG su2HermBasis).add_mem (casimir_mem_adCommutantGG su2HermBasis)
    ((adCommutantGG su2HermBasis).smul_mem _ one_mem_su2_adCommutantGG)

/-- The strict single-qubit Clifford lift is doubled-commutant complete for `su(2)`. -/
lemma qubitClifford_isDoubledCommutantComplete :
    IsDoubledCommutantComplete qubitClifford su2HermBasis := by
  intro M hM
  rw [TwirlInternal.qubitClifford_commutant_normal_form M hM]
  exact (adCommutantGG su2HermBasis).add_mem
    ((adCommutantGG su2HermBasis).smul_mem _ one_mem_su2_adCommutantGG)
    ((adCommutantGG su2HermBasis).smul_mem _ qubitSwap_mem_su2_adCommutantGG)

/-- Commuting with the finite doubled Clifford action implies Lie-algebra doubled invariance. -/
lemma qubitClifford_bridge
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : ∀ g, (qubitClifford g ⊗ₖ qubitClifford g) * M =
      M * (qubitClifford g ⊗ₖ qubitClifford g)) :
    M ∈ adCommutantGG su2HermBasis :=
  qubitClifford_isDoubledCommutantComplete M hM

end QuantumAlg.QubitTwoDesign

end
