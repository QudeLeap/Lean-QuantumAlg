/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Util.FinPow
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Raw tensor products

This module defines tensor products for unrestricted state vectors and Hilbert
operators.  It makes no normalization or unitarity claim.
-/

section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace HilbertVector

noncomputable section

/-- Tensor product of raw Hilbert-space vectors. -/
public def tensor (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    HilbertVector (Qubits (m + n)) :=
  WithLp.toLp 2 fun i => ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2

@[simp]
theorem tensor_apply (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n))
    (i : Fin (2 ^ (m + n))) :
    tensor ψ φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

theorem tensor_apply_prod (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n))
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    tensor ψ φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

@[simp]
theorem add_tensor (ψ ψ' : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    tensor (ψ + ψ') φ = tensor ψ φ + tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ + ψ') φ i = (tensor ψ φ + tensor ψ' φ) i
  simp [add_mul]

@[simp]
theorem sub_tensor (ψ ψ' : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    tensor (ψ - ψ') φ = tensor ψ φ - tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ - ψ') φ i = (tensor ψ φ - tensor ψ' φ) i
  simp [sub_mul]

@[simp]
theorem smul_tensor (c : ℂ) (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    tensor (c • ψ) φ = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (c • ψ) φ i = (c • tensor ψ φ) i
  simp [mul_assoc]

@[simp]
theorem tensor_add (ψ : HilbertVector (Qubits m)) (φ φ' : HilbertVector (Qubits n)) :
    tensor ψ (φ + φ') = tensor ψ φ + tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ + φ') i = (tensor ψ φ + tensor ψ φ') i
  simp [mul_add]

@[simp]
theorem tensor_sub (ψ : HilbertVector (Qubits m)) (φ φ' : HilbertVector (Qubits n)) :
    tensor ψ (φ - φ') = tensor ψ φ - tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ - φ') i = (tensor ψ φ - tensor ψ φ') i
  simp [mul_sub]

@[simp]
theorem tensor_smul (c : ℂ) (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    tensor ψ (c • φ) = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (c • φ) i = (c • tensor ψ φ) i
  simp [mul_left_comm]

@[simp]
theorem neg_tensor (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    tensor (-ψ) φ = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (-ψ) φ i = (-tensor ψ φ) i
  simp [tensor_apply]

@[simp]
theorem tensor_neg (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    tensor ψ (-φ) = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (-φ) i = (-tensor ψ φ) i
  simp [tensor_apply]

@[simp]
theorem zero_tensor (φ : HilbertVector (Qubits n)) :
    tensor (0 : HilbertVector (Qubits m)) φ = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (0 : HilbertVector (Qubits m)) φ i = (0 : HilbertVector (Qubits (m + n))) i
  simp [tensor_apply]

@[simp]
theorem tensor_zero (ψ : HilbertVector (Qubits m)) :
    tensor ψ (0 : HilbertVector (Qubits n)) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (0 : HilbertVector (Qubits n)) i = (0 : HilbertVector (Qubits (m + n))) i
  simp [tensor_apply]

/-- The norm is multiplicative under tensor products. -/
theorem norm_tensor (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)) :
    ‖tensor ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i, ‖ψ i‖ ^ 2 from
      Finset.sum_nonneg fun i _ => sq_nonneg ‖ψ i‖)]
  congr 1
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => ‖tensor ψ φ i‖ ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]

/-- The inner product factors over tensor products. -/
theorem inner_tensor_tensor (ψ ψ' : HilbertVector (Qubits m))
    (φ φ' : HilbertVector (Qubits n)) :
    inner ℂ (tensor ψ φ) (tensor ψ' φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => tensor ψ' φ' i * starRingEnd ℂ (tensor ψ φ i)),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, tensor_apply, Equiv.symm_apply_apply, map_mul,
    mul_mul_mul_comm]

end

end HilbertVector

namespace HilbertOperator

noncomputable section

/-- Tensor product of unrestricted Hilbert-space operators. -/
public def tensor (G : HilbertOperator (Qubits m)) (K : HilbertOperator (Qubits n)) :
    HilbertOperator (Qubits (m + n)) :=
  Matrix.reindex prodEquiv prodEquiv (G ⊗ₖ K)

@[simp]
theorem tensor_apply (G : HilbertOperator (Qubits m)) (K : HilbertOperator (Qubits n))
    (i j : Fin (2 ^ (m + n))) :
    tensor G K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl

@[simp]
theorem zero_tensor (K : HilbertOperator (Qubits n)) :
    tensor (0 : HilbertOperator (Qubits m)) K = 0 := by
  ext i j
  simp [tensor_apply]

@[simp]
theorem tensor_zero (G : HilbertOperator (Qubits m)) :
    tensor G (0 : HilbertOperator (Qubits n)) = 0 := by
  ext i j
  simp [tensor_apply]

theorem add_tensor (G G' : HilbertOperator (Qubits m)) (K : HilbertOperator (Qubits n)) :
    tensor (G + G') K = tensor G K + tensor G' K := by
  ext i j
  simp [tensor_apply, add_mul]

theorem tensor_add (G : HilbertOperator (Qubits m)) (K K' : HilbertOperator (Qubits n)) :
    tensor G (K + K') = tensor G K + tensor G K' := by
  ext i j
  simp [tensor_apply, mul_add]

theorem tensor_mul_tensor (G G' : HilbertOperator (Qubits m))
    (K K' : HilbertOperator (Qubits n)) :
    tensor G K * tensor G' K' = tensor (G * G') (K * K') := by
  rw [tensor, tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]

theorem conjTranspose_tensor (G : HilbertOperator (Qubits m))
    (K : HilbertOperator (Qubits n)) :
    (tensor G K).conjTranspose = tensor G.conjTranspose K.conjTranspose := by
  rw [tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

@[simp]
theorem one_tensor_one :
    tensor (1 : HilbertOperator (Qubits m)) (1 : HilbertOperator (Qubits n)) = 1 := by
  rw [tensor, Matrix.one_kronecker_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

theorem tensor_applyVec_tensor (G : HilbertOperator (Qubits m))
    (K : HilbertOperator (Qubits n)) (ψ : HilbertVector (Qubits m))
    (φ : HilbertVector (Qubits n)) :
    applyVec (tensor G K) (HilbertVector.tensor ψ φ)
      = HilbertVector.tensor (applyVec G ψ) (applyVec K φ) := by
  apply WithLp.ofLp_injective
  funext i
  change applyVec (tensor G K) (HilbertVector.tensor ψ φ) i
      = HilbertVector.tensor (applyVec G ψ) (applyVec K φ) i
  rw [HilbertVector.tensor_apply, applyVec_apply, applyVec_apply, applyVec_apply,
    Finset.sum_mul_sum,
    ← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun j => tensor G K i j * HilbertVector.tensor ψ φ j),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, HilbertVector.tensor_apply, Equiv.symm_apply_apply,
    mul_mul_mul_comm]

end

end HilbertOperator

end QuantumAlg

end
