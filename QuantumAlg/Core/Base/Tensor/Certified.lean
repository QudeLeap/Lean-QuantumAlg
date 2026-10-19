/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Invariant-preserving tensor products

Tensoring normalized vectors preserves normalization, and tensoring unitary
operators preserves unitarity.  The certified values in this module carry no
physical placement or resource metadata.
-/

section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace NormalizedVector

noncomputable section

/-- Tensor product of metadata-free normalized vectors. -/
public def tensor (ψ : NormalizedVector (Qubits m)) (φ : NormalizedVector (Qubits n)) :
    NormalizedVector (Qubits (m + n)) :=
  ofVector
    (HilbertVector.tensor (ψ : HilbertVector (Qubits m)) (φ : HilbertVector (Qubits n)))
    (by
      rw [HilbertVector.norm_tensor, ψ.norm_eq_one, φ.norm_eq_one, one_mul])

@[simp]
lemma coe_tensor (ψ : NormalizedVector (Qubits m))
    (φ : NormalizedVector (Qubits n)) :
    ((ψ.tensor φ : NormalizedVector (Qubits (m + n))) :
      HilbertVector (Qubits (m + n))) =
      HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n)) := rfl

@[simp]
lemma tensor_apply (ψ : NormalizedVector (Qubits m))
    (φ : NormalizedVector (Qubits n)) (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

lemma tensor_apply_prod (ψ : NormalizedVector (Qubits m))
    (φ : NormalizedVector (Qubits n)) (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

/-- Computational-basis kets tensor to the corresponding product basis ket. -/
lemma tensor_ket (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    (ket x).tensor (ket y) = ket (prodEquiv (x, y)) := by
  apply NormalizedVector.ext
  intro i
  rw [tensor_apply, ket_apply, ket_apply, ket_apply]
  by_cases h : i = prodEquiv (x, y)
  · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply]),
      if_pos (by rw [h, Equiv.symm_apply_apply]), one_mul]
  · have h' : ¬((prodEquiv.symm i).1 = x ∧ (prodEquiv.symm i).2 = y) := by
      rintro ⟨h1, h2⟩
      exact h (by
        rw [← Equiv.apply_symm_apply (prodEquiv (m := m) (n := n)) i]
        exact congrArg prodEquiv (Prod.ext h1 h2))
    rw [if_neg h]
    rcases not_and_or.mp h' with h1 | h2
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h2, mul_zero]

lemma norm_tensor (ψ : NormalizedVector (Qubits m))
    (φ : NormalizedVector (Qubits n)) :
    ‖ψ.tensor φ‖ = ‖ψ‖ * ‖φ‖ := by
  change
    ‖HilbertVector.tensor (ψ : HilbertVector (Qubits m))
      (φ : HilbertVector (Qubits n))‖ =
      ‖(ψ : HilbertVector (Qubits m))‖ * ‖(φ : HilbertVector (Qubits n))‖
  rw [HilbertVector.norm_tensor]

lemma inner_tensor_tensor (ψ ψ' : NormalizedVector (Qubits m))
    (φ φ' : NormalizedVector (Qubits n)) :
    inner ℂ (ψ.tensor φ) (ψ'.tensor φ') =
      inner ℂ ψ ψ' * inner ℂ φ φ' := by
  change inner ℂ
      (HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n)))
      (HilbertVector.tensor (ψ' : HilbertVector (Qubits m))
        (φ' : HilbertVector (Qubits n))) =
    inner ℂ (ψ : HilbertVector (Qubits m)) (ψ' : HilbertVector (Qubits m)) *
      inner ℂ (φ : HilbertVector (Qubits n)) (φ' : HilbertVector (Qubits n))
  rw [HilbertVector.inner_tensor_tensor]

end

end NormalizedVector

namespace HilbertVector

noncomputable section

/-- Tensor product of raw vectors over arbitrary finite registers. -/
@[expose] public def prodTensor {R S : Register}
    (left : HilbertVector R) (right : HilbertVector S) :
    HilbertVector (Register.prod R S) :=
  WithLp.toLp 2 fun index => left index.1 * right index.2

@[simp] public lemma prodTensor_apply {R S : Register}
    (left : HilbertVector R) (right : HilbertVector S)
    (index : (Register.prod R S).Index) :
    prodTensor left right index = left index.1 * right index.2 :=
  rfl

/-- The norm of an arbitrary finite-register product vector is the product of
the subsystem norms. -/
public lemma norm_prodTensor {R S : Register}
    (left : HilbertVector R) (right : HilbertVector S) :
    ‖prodTensor left right‖ = ‖left‖ * ‖right‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ index, ‖left index‖ ^ 2 from
      Finset.sum_nonneg fun index _ => sq_nonneg ‖left index‖)]
  congr 1
  simp only [prodTensor_apply]
  change (∑ index : R.Index × S.Index,
      ‖left index.1 * right index.2‖ ^ 2) =
    (∑ leftIndex : R.Index, ‖left leftIndex‖ ^ 2) *
      ∑ rightIndex : S.Index, ‖right rightIndex‖ ^ 2
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun leftIndex _ =>
    Finset.sum_congr rfl fun rightIndex _ => ?_
  rw [norm_mul, mul_pow]

/-- Computational-basis vectors form the corresponding product-register basis vector. -/
@[simp] public lemma prodTensor_ket {R S : Register}
    (left : R.Index) (right : S.Index) :
    prodTensor
        (NormalizedVector.ket (R := R) left : HilbertVector R)
        (NormalizedVector.ket (R := S) right : HilbertVector S) =
      (NormalizedVector.ket (R := Register.prod R S) (left, right) :
        HilbertVector (Register.prod R S)) := by
  apply WithLp.ofLp_injective
  funext index
  by_cases same : index = (left, right)
  · subst index
    simp [NormalizedVector.ket_apply]
  · have component : index.1 ≠ left ∨ index.2 ≠ right := by
      apply not_and_or.mp
      rintro ⟨leftSame, rightSame⟩
      exact same (Prod.ext leftSame rightSame)
    rcases component with leftDifferent | rightDifferent
    · simp [NormalizedVector.ket_apply, same, leftDifferent]
    · simp [NormalizedVector.ket_apply, same, rightDifferent]

end

end HilbertVector

namespace NormalizedVector

noncomputable section

/-- Tensor product of normalized vectors over arbitrary finite registers. -/
@[expose] public def prodTensor {R S : Register}
    (left : NormalizedVector R) (right : NormalizedVector S) :
    NormalizedVector (Register.prod R S) :=
  ofVector (HilbertVector.prodTensor left.vec right.vec) (by
    rw [HilbertVector.norm_prodTensor, left.norm_eq_one, right.norm_eq_one, one_mul])

@[simp] public lemma prodTensor_apply {R S : Register}
    (left : NormalizedVector R) (right : NormalizedVector S)
    (index : (Register.prod R S).Index) :
    prodTensor left right index = left index.1 * right index.2 :=
  rfl

end

end NormalizedVector

namespace UnitaryOperator

noncomputable section

/-- Tensor product over arbitrary finite registers, indexed by their product register. -/
public def prodTensor {R S : Register} (U : UnitaryOperator R) (V : UnitaryOperator S) :
    UnitaryOperator (Register.prod R S) :=
  ofMatrix
    (Matrix.reindex (Register.prodIndexEquiv R S) (Register.prodIndexEquiv R S)
      ((U : HilbertOperator R) ⊗ₖ (V : HilbertOperator S))) (by
    have hU := U.property
    have hV := V.property
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU hV ⊢
    rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.conjTranspose_kronecker, Matrix.submatrix_mul_equiv,
      ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one,
      Matrix.submatrix_one_equiv])

@[simp]
lemma coe_prodTensor {R S : Register} (U : UnitaryOperator R)
    (V : UnitaryOperator S) :
    ((prodTensor U V : UnitaryOperator (Register.prod R S)) :
      HilbertOperator (Register.prod R S)) =
      Matrix.reindex (Register.prodIndexEquiv R S) (Register.prodIndexEquiv R S)
        ((U : HilbertOperator R) ⊗ₖ (V : HilbertOperator S)) := rfl

@[simp]
lemma prodTensor_apply {R S : Register} (U : UnitaryOperator R)
    (V : UnitaryOperator S) (i j : (Register.prod R S).Index) :
    prodTensor U V i j = U i.1 j.1 * V i.2 j.2 := by
  change
    (Matrix.reindex (Register.prodIndexEquiv R S) (Register.prodIndexEquiv R S)
      ((U : HilbertOperator R) ⊗ₖ (V : HilbertOperator S))) i j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

/-- Every product-register entry is the product of the two actual subsystem entries. -/
public lemma unitaryOperator_prodTensor_apply {R S : Register} (U : UnitaryOperator R)
    (V : UnitaryOperator S) (i j : (Register.prod R S).Index) :
    prodTensor U V i j = U i.1 j.1 * V i.2 j.2 :=
  prodTensor_apply U V i j

/-- Product operators act factorwise on raw vectors over arbitrary finite
registers. -/
public lemma prodTensor_applyVec_prodTensor {R S : Register}
    (U : UnitaryOperator R) (V : UnitaryOperator S)
    (left : HilbertVector R) (right : HilbertVector S) :
    (prodTensor U V).applyVec (HilbertVector.prodTensor left right) =
      HilbertVector.prodTensor (U.applyVec left) (V.applyVec right) := by
  apply WithLp.ofLp_injective
  funext index
  rw [applyVec_apply, HilbertVector.prodTensor_apply,
    applyVec_apply, applyVec_apply]
  change (∑ source : R.Index × S.Index,
      U index.1 source.1 * V index.2 source.2 *
        (left source.1 * right source.2)) =
    (∑ sourceLeft, U index.1 sourceLeft * left sourceLeft) *
      ∑ sourceRight, V index.2 sourceRight * right sourceRight
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro sourceLeft _
  apply Finset.sum_congr rfl
  intro sourceRight _
  ring

/-- Tensor product of metadata-free unitary operators. -/
public def tensor (U : UnitaryOperator (Qubits m)) (V : UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (m + n)) :=
  ofMatrix
    (HilbertOperator.tensor (U : HilbertOperator (Qubits m))
      (V : HilbertOperator (Qubits n)))
    (by
      have hU := U.property
      have hV := V.property
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU hV ⊢
      rw [HilbertOperator.tensor, Matrix.reindex_apply,
        Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
        Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, hU, hV,
        Matrix.one_kronecker_one, Matrix.submatrix_one_equiv])

@[simp]
lemma coe_tensor (U : UnitaryOperator (Qubits m))
    (V : UnitaryOperator (Qubits n)) :
    ((U.tensor V : UnitaryOperator (Qubits (m + n))) :
      HilbertOperator (Qubits (m + n))) =
      HilbertOperator.tensor (U : HilbertOperator (Qubits m))
        (V : HilbertOperator (Qubits n)) := rfl

@[simp]
lemma tensor_apply (U : UnitaryOperator (Qubits m))
    (V : UnitaryOperator (Qubits n)) (i j : Fin (2 ^ (m + n))) :
    U.tensor V i j =
      U (prodEquiv.symm i).1 (prodEquiv.symm j).1 *
        V (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl

lemma tensor_applyVec_tensor (U : UnitaryOperator (Qubits m))
    (V : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits m))
    (φ : HilbertVector (Qubits n)) :
    (U.tensor V).applyVec (HilbertVector.tensor ψ φ) =
      HilbertVector.tensor (U.applyVec ψ) (V.applyVec φ) :=
  HilbertOperator.tensor_applyVec_tensor (U : HilbertOperator (Qubits m))
    (V : HilbertOperator (Qubits n)) ψ φ

lemma tensor_apply_tensor (U : UnitaryOperator (Qubits m))
    (V : UnitaryOperator (Qubits n)) (ψ : NormalizedVector (Qubits m))
    (φ : NormalizedVector (Qubits n)) :
    (U.tensor V).apply (ψ.tensor φ) =
      (U.apply ψ).tensor (V.apply φ) := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (U : HilbertOperator (Qubits m))
        (V : HilbertOperator (Qubits n)))
      (HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n))) i =
    HilbertVector.tensor
      (HilbertOperator.applyVec (U : HilbertOperator (Qubits m))
        (ψ : HilbertVector (Qubits m)))
      (HilbertOperator.applyVec (V : HilbertOperator (Qubits n))
        (φ : HilbertVector (Qubits n))) i
  rw [HilbertOperator.tensor_applyVec_tensor]

end

end UnitaryOperator

end QuantumAlg

end
