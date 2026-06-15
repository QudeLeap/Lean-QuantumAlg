/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Gate
public import QuantumAlg.Util.FinPow
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensor products of states and gates

Tensor (Kronecker) products composing an `m`-qubit and an `n`-qubit system
into an `(m + n)`-qubit system.

## Conventions

- The first factor holds the lower-index qubits, i.e. the *most significant*
  bits of the joint basis label (big-endian, matching `QuantumAlg.PureState`):
  the joint label of `x : Fin (2 ^ m)` and `y : Fin (2 ^ n)` is
  `y + 2 ^ n * x`, written `prodEquiv (x, y)`.
- `Matrix.kroneckerMap (· * ·)` (notation `⊗ₖ`, scoped to `Kronecker`) is
  indexed by pairs; `Gate.tensor` reindexes it along `prodEquiv` so that
  composite gates act on `PureState (m + n)` directly.

## Main definitions

- `QuantumAlg.prodEquiv` (from `QuantumAlg.Util.FinPow`) —
  `Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n))`, the big-endian index pairing.
- `QuantumAlg.PureState.tensor` — tensor product of states;
  `tensor_ket` computes it on basis kets, `norm_tensor` shows
  `‖ψ ⊗ φ‖ = ‖ψ‖ * ‖φ‖`.
- `QuantumAlg.Gate.tensor` — tensor product of gates;
  `Gate.tensor_mem_unitaryGroup` closes unitarity under `⊗`, and the
  mixed-product law `Gate.tensor_apply_tensor` shows
  `(G ⊗ K)(ψ ⊗ φ) = (G ψ) ⊗ (K φ)`. Gate tensors also satisfy the
  matrix-level algebra: bilinearity, `Gate.tensor_mul_tensor`,
  `Gate.conjTranspose_tensor`, `Gate.one_tensor_one`.

Pinned Mathlib API:
`Matrix.kroneckerMap` (`⊗ₖ`, `kroneckerMap_apply`, `mul_kronecker_mul`,
`one_kronecker_one`, `conjTranspose_kronecker`), `Matrix.reindex`
(`reindex_apply`, `submatrix_mul_equiv`, `conjTranspose_submatrix`,
`submatrix_one_equiv`), `Equiv.sum_comp`, `Fintype.sum_prod_type`.
-/

@[expose] public section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace PureState

noncomputable section

/-- Tensor product of pure states: `(ψ.tensor φ) (prodEquiv (x, y)) = ψ x * φ y`. -/
def tensor (ψ : PureState m) (φ : PureState n) : PureState (m + n) :=
  WithLp.toLp 2 fun i => ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2

@[simp]
theorem tensor_apply (ψ : PureState m) (φ : PureState n)
    (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

theorem tensor_apply_prod (ψ : PureState m) (φ : PureState n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

/-! ### Bilinearity -/

@[simp]
theorem add_tensor (ψ ψ' : PureState m) (φ : PureState n) :
    (ψ + ψ').tensor φ = ψ.tensor φ + ψ'.tensor φ := by
  apply WithLp.ofLp_injective
  funext i
  change (ψ + ψ').tensor φ i = (ψ.tensor φ + ψ'.tensor φ) i
  simp [add_mul]

@[simp]
theorem sub_tensor (ψ ψ' : PureState m) (φ : PureState n) :
    (ψ - ψ').tensor φ = ψ.tensor φ - ψ'.tensor φ := by
  apply WithLp.ofLp_injective
  funext i
  change (ψ - ψ').tensor φ i = (ψ.tensor φ - ψ'.tensor φ) i
  simp [sub_mul]

@[simp]
theorem smul_tensor (c : ℂ) (ψ : PureState m) (φ : PureState n) :
    (c • ψ).tensor φ = c • ψ.tensor φ := by
  apply WithLp.ofLp_injective
  funext i
  change (c • ψ).tensor φ i = (c • ψ.tensor φ) i
  simp [mul_assoc]

@[simp]
theorem tensor_add (ψ : PureState m) (φ φ' : PureState n) :
    ψ.tensor (φ + φ') = ψ.tensor φ + ψ.tensor φ' := by
  apply WithLp.ofLp_injective
  funext i
  change ψ.tensor (φ + φ') i = (ψ.tensor φ + ψ.tensor φ') i
  simp [mul_add]

@[simp]
theorem tensor_sub (ψ : PureState m) (φ φ' : PureState n) :
    ψ.tensor (φ - φ') = ψ.tensor φ - ψ.tensor φ' := by
  apply WithLp.ofLp_injective
  funext i
  change ψ.tensor (φ - φ') i = (ψ.tensor φ - ψ.tensor φ') i
  simp [mul_sub]

@[simp]
theorem tensor_smul (c : ℂ) (ψ : PureState m) (φ : PureState n) :
    ψ.tensor (c • φ) = c • ψ.tensor φ := by
  apply WithLp.ofLp_injective
  funext i
  change ψ.tensor (c • φ) i = (c • ψ.tensor φ) i
  simp [mul_left_comm]

@[simp]
theorem neg_tensor (ψ : PureState m) (φ : PureState n) :
    (-ψ).tensor φ = -ψ.tensor φ := by
  apply WithLp.ofLp_injective
  funext i
  change (-ψ).tensor φ i = (-ψ.tensor φ) i
  simp [tensor_apply]

@[simp]
theorem tensor_neg (ψ : PureState m) (φ : PureState n) :
    ψ.tensor (-φ) = -ψ.tensor φ := by
  apply WithLp.ofLp_injective
  funext i
  change ψ.tensor (-φ) i = (-ψ.tensor φ) i
  simp [tensor_apply]

@[simp]
theorem zero_tensor (φ : PureState n) :
    (0 : PureState m).tensor φ = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change (0 : PureState m).tensor φ i = (0 : PureState (m + n)) i
  simp [tensor_apply]

@[simp]
theorem tensor_zero (ψ : PureState m) :
    ψ.tensor (0 : PureState n) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change ψ.tensor (0 : PureState n) i = (0 : PureState (m + n)) i
  simp [tensor_apply]

/-- Basis kets tensor to basis kets: `|x⟩ ⊗ |y⟩ = |xy⟩`. -/
theorem tensor_ket (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    (ket x).tensor (ket y) = ket (prodEquiv (x, y)) := by
  apply WithLp.ofLp_injective
  funext i
  change (ket x).tensor (ket y) i = ket (prodEquiv (x, y)) i
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

/-- The norm is multiplicative under tensor products; in particular the
tensor product of normalized states is normalized. -/
theorem norm_tensor (ψ : PureState m) (φ : PureState n) :
    ‖ψ.tensor φ‖ = ‖ψ‖ * ‖φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i, ‖ψ i‖ ^ 2 from
      Finset.sum_nonneg fun i _ => sq_nonneg ‖ψ i‖)]
  congr 1
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => ‖ψ.tensor φ i‖ ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]

/-- The inner product factors over tensor products:
`⟨ψ ⊗ φ, ψ' ⊗ φ'⟩ = ⟨ψ, ψ'⟩ · ⟨φ, φ'⟩`. -/
theorem inner_tensor_tensor (ψ ψ' : PureState m) (φ φ' : PureState n) :
    inner ℂ (ψ.tensor φ) (ψ'.tensor φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => (ψ'.tensor φ') i * starRingEnd ℂ (ψ.tensor φ i)),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, tensor_apply, Equiv.symm_apply_apply, map_mul,
    mul_mul_mul_comm]

end

end PureState

namespace Gate

noncomputable section

/-- Tensor (Kronecker) product of gates, reindexed to act on
`PureState (m + n)`. -/
def tensor (G : Gate m) (K : Gate n) : Gate (m + n) :=
  Matrix.reindex prodEquiv prodEquiv (G ⊗ₖ K)

@[simp]
theorem tensor_apply (G : Gate m) (K : Gate n)
    (i j : Fin (2 ^ (m + n))) :
    G.tensor K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 :=
  rfl

/-! ### Algebra of gate tensors -/

@[simp]
theorem zero_tensor (K : Gate n) : (0 : Gate m).tensor K = 0 := by
  ext i j
  simp [tensor_apply]

@[simp]
theorem tensor_zero (G : Gate m) : G.tensor (0 : Gate n) = 0 := by
  ext i j
  simp [tensor_apply]

theorem add_tensor (G G' : Gate m) (K : Gate n) :
    (G + G').tensor K = G.tensor K + G'.tensor K := by
  ext i j
  simp [tensor_apply, add_mul]

theorem tensor_add (G : Gate m) (K K' : Gate n) :
    G.tensor (K + K') = G.tensor K + G.tensor K' := by
  ext i j
  simp [tensor_apply, mul_add]

/-- Mixed-product law at the matrix level:
`(G ⊗ K) (G' ⊗ K') = (G G') ⊗ (K K')`. -/
theorem tensor_mul_tensor (G G' : Gate m) (K K' : Gate n) :
    G.tensor K * G'.tensor K' = tensor (G * G') (K * K') := by
  rw [tensor, tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]

/-- Conjugate transpose distributes over gate tensors. -/
theorem conjTranspose_tensor (G : Gate m) (K : Gate n) :
    (G.tensor K).conjTranspose
      = tensor G.conjTranspose K.conjTranspose := by
  rw [tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

@[simp]
theorem one_tensor_one : (1 : Gate m).tensor (1 : Gate n) = 1 := by
  rw [tensor, Matrix.one_kronecker_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

/-- Unitarity is preserved by tensor products. -/
theorem tensor_mem_unitaryGroup {G : Gate m} {K : Gate n}
    (hG : G ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    G.tensor K ∈ Matrix.unitaryGroup (Fin (2 ^ (m + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hG hK ⊢
  rw [tensor, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, hG, hK, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- Mixed-product law: `(G ⊗ K)(ψ ⊗ φ) = (G ψ) ⊗ (K φ)`. Composite circuits
factor through per-subsystem actions. -/
theorem tensor_apply_tensor (G : Gate m) (K : Gate n)
    (ψ : PureState m) (φ : PureState n) :
    (G.tensor K).apply (ψ.tensor φ) = (G.apply ψ).tensor (K.apply φ) := by
  apply WithLp.ofLp_injective
  funext i
  change (G.tensor K).apply (ψ.tensor φ) i
      = (G.apply ψ).tensor (K.apply φ) i
  rw [PureState.tensor_apply, apply_apply, apply_apply, apply_apply,
    Finset.sum_mul_sum,
    ← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun j => G.tensor K i j * ψ.tensor φ j),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, PureState.tensor_apply, Equiv.symm_apply_apply,
    mul_mul_mul_comm]

end

end Gate

end QuantumAlg
