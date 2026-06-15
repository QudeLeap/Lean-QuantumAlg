/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.State
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Qubit gates

An `n`-qubit gate is a `2^n × 2^n` complex matrix, acting on a pure state by
matrix-vector multiplication. Gates used in theorems are unitary
(`Matrix.unitaryGroup`), stated per gate (`H_mem_unitaryGroup`, …), not
bundled in the type.

## Conventions

- A gate `G : Gate n` acts on `ψ : PureState n` as `G.apply ψ`, the
  matrix-vector product `G *ᵥ ψ` (Schrodinger picture; circuits compose by
  matrix multiplication, rightmost factor acts first).
- Row/column indices follow the big-endian basis labelling of
  `QuantumAlg.PureState`.
- Permutation gates (`X`, `CNOT`, oracles, …) are built with `Gate.ofPerm`,
  which gives their unitarity and basis action for free.

## Main definitions

- `QuantumAlg.Gate n` — `Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ`.
- `Gate.apply` — action on a state; linear in the state.
- `Gate.ofPerm σ` — the permutation gate of `σ : Equiv.Perm (Fin (2 ^ n))`.
The named gates (`H`, `X`, `Y`, `Z`, and the two-qubit `CNOT`) and their
unitarity/action lemmas now live in `QuantumAlg.Core.Components.Gates`.

Pinned Mathlib API: `Matrix.mulVec` (and `mulVec_add/smul/single_one`,
`one_mulVec`, `mulVec_mulVec`), `Matrix.mem_unitaryGroup_iff`,
`Equiv.Perm.permMatrix` (and `Matrix.permMatrix_mulVec`,
`Matrix.conjTranspose_permMatrix`, `Matrix.permMatrix_mul`,
`Matrix.permMatrix_one`), `Finset.sum_ite_eq'`.
-/

@[expose] public section

namespace QuantumAlg

open PureState

/-- The space of `n`-qubit gates: `2^n × 2^n` complex matrices. Gates used in
theorems are unitary (see the `*_mem_unitaryGroup` lemmas); the type itself
does not enforce it. -/
abbrev Gate (n : ℕ) : Type := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

namespace Gate

noncomputable section

variable {n : ℕ}

/-- A gate acts on a pure state by matrix-vector multiplication. -/
def apply (G : Gate n) (ψ : PureState n) : PureState n :=
  WithLp.toLp 2 (G.mulVec ψ.ofLp)

@[simp]
theorem apply_apply (G : Gate n) (ψ : PureState n) (i : Fin (2 ^ n)) :
    G.apply ψ i = ∑ j, G i j * ψ j :=
  rfl

@[simp]
theorem apply_add (G : Gate n) (ψ φ : PureState n) :
    G.apply (ψ + φ) = G.apply ψ + G.apply φ := by
  unfold apply
  rw [show (ψ + φ).ofLp = ψ.ofLp + φ.ofLp from rfl, Matrix.mulVec_add]
  rfl

@[simp]
theorem apply_sub (G : Gate n) (ψ φ : PureState n) :
    G.apply (ψ - φ) = G.apply ψ - G.apply φ := by
  unfold apply
  rw [show (ψ - φ).ofLp = ψ.ofLp - φ.ofLp from rfl, Matrix.mulVec_sub]
  rfl

@[simp]
theorem apply_smul (G : Gate n) (c : ℂ) (ψ : PureState n) :
    G.apply (c • ψ) = c • G.apply ψ := by
  unfold apply
  rw [show (c • ψ).ofLp = c • ψ.ofLp from rfl, Matrix.mulVec_smul]
  rfl

@[simp]
theorem apply_neg (G : Gate n) (ψ : PureState n) :
    G.apply (-ψ) = -G.apply ψ := by
  unfold apply
  rw [show (-ψ).ofLp = -ψ.ofLp from rfl, Matrix.mulVec_neg]
  rfl

@[simp]
theorem add_apply (G K : Gate n) (ψ : PureState n) :
    (G + K).apply ψ = G.apply ψ + K.apply ψ := by
  unfold apply
  rw [Matrix.add_mulVec]
  rfl

@[simp]
theorem one_apply (ψ : PureState n) : (1 : Gate n).apply ψ = ψ := by
  unfold apply
  rw [Matrix.one_mulVec]

theorem mul_apply (G₁ G₂ : Gate n) (ψ : PureState n) :
    apply (G₁ * G₂) ψ = G₁.apply (G₂.apply ψ) := by
  unfold apply
  rw [show (WithLp.toLp 2 (G₂.mulVec ψ.ofLp)).ofLp = G₂.mulVec ψ.ofLp from rfl,
    Matrix.mulVec_mulVec]

/-- A gate sends the basis ket `|x⟩` to its `x`-th column. -/
@[simp]
theorem apply_ket (G : Gate n) (x : Fin (2 ^ n)) (i : Fin (2 ^ n)) :
    G.apply (ket x) i = G i x := by
  rw [apply_apply]
  simp only [ket_apply, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' x (fun j => G i j)

/-! ## Permutation gates -/

/-- The gate permuting the computational basis by `σ`:
`(ofPerm σ).apply (ket x) = ket (σ⁻¹ x)`. Unitary by construction. -/
def ofPerm (σ : Equiv.Perm (Fin (2 ^ n))) : Gate n :=
  σ.permMatrix ℂ

@[simp]
theorem ofPerm_apply (σ : Equiv.Perm (Fin (2 ^ n))) (ψ : PureState n)
    (i : Fin (2 ^ n)) : (ofPerm σ).apply ψ i = ψ (σ i) := by
  unfold apply ofPerm
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem ofPerm_apply_ket (σ : Equiv.Perm (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    (ofPerm σ).apply (ket x) = ket (σ⁻¹ x) := by
  apply WithLp.ofLp_injective
  funext i
  rw [show ((ofPerm σ).apply (ket x)).ofLp i = (ofPerm σ).apply (ket x) i
      from rfl,
    show (ket (σ⁻¹ x)).ofLp i = ket (σ⁻¹ x) i from rfl,
    ofPerm_apply, ket_apply, ket_apply]
  by_cases h : σ i = x
  · rw [if_pos h, if_pos (by rw [← h]; exact (Equiv.symm_apply_apply σ i).symm)]
  · rw [if_neg h,
      if_neg (fun hi => h (by rw [hi]; exact Equiv.apply_symm_apply σ x))]

theorem ofPerm_mem_unitaryGroup (σ : Equiv.Perm (Fin (2 ^ n))) :
    ofPerm σ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ofPerm, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, Matrix.permMatrix_one]

/-! ## Unitary gates preserve inner products and norms -/

/-- Unitary gates preserve the inner product. -/
theorem inner_apply_apply_of_mem_unitaryGroup {U : Gate n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ φ : PureState n) :
    inner ℂ (U.apply ψ) (U.apply φ) = inner ℂ ψ φ := by
  have hUU : U.conjTranspose * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  simp only [PiLp.inner_apply, RCLike.inner_apply, apply_apply]
  calc ∑ i, (∑ k, U i k * φ k) * starRingEnd ℂ (∑ j, U i j * ψ j)
      = ∑ i, ∑ k, ∑ j, (U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (1 : Gate n) j k * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [← hUU, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (U i j) = starRingEnd ℂ (U i j) from rfl, mul_comm]
    _ = ∑ k, φ k * starRingEnd ℂ (ψ k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        exact Fintype.sum_ite_eq' k fun j => φ k * starRingEnd ℂ (ψ j)

/-- Unitary gates preserve the norm: gates evolve normalized states to
normalized states. -/
theorem norm_apply_of_mem_unitaryGroup {U : Gate n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ : PureState n) :
    ‖U.apply ψ‖ = ‖ψ‖ := by
  have h := inner_apply_apply_of_mem_unitaryGroup hU ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖U.apply ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  calc ‖U.apply ψ‖ = √(‖U.apply ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(‖ψ‖ ^ 2) := by rw [h2]
    _ = ‖ψ‖ := Real.sqrt_sq (norm_nonneg _)

end

end Gate

end QuantumAlg
