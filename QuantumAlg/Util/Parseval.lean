/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthogonal decomposition utilities

Wraps Mathlib's `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`
for `EuclideanSpace ℂ ι` (Util layer — no Core imports).
-/

@[expose] public section

namespace QuantumAlg

open scoped Real
open Complex

noncomputable section

/-- ‖u + v‖² = ‖u‖² + ‖v‖² when u ⟂ v. -/
lemma norm_sq_add_of_inner_eq_zero {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℂ ι) (h_orth : inner ℂ u v = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  by simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v h_orth

/-- ‖c·e₀ + v_orth‖² = |c|²·‖e₀‖² + ‖v_orth‖² when e₀ ⟂ v_orth. -/
lemma norm_sq_smul_add_of_inner_eq_zero {ι : Type*} [Fintype ι]
    (c : ℂ) (e₀ v_orth : EuclideanSpace ℂ ι)
    (h_orth : inner ℂ e₀ v_orth = 0) :
    ‖c • e₀ + v_orth‖ ^ 2 = Complex.normSq c * ‖e₀‖ ^ 2 + ‖v_orth‖ ^ 2 := by
  have h_orth_smul : inner ℂ (c • e₀) v_orth = 0 := by
    simp [inner_smul_left, h_orth]
  rw [norm_sq_add_of_inner_eq_zero (c • e₀) v_orth h_orth_smul]
  rw [norm_smul, mul_pow]
  rw [← Complex.normSq_eq_norm_sq]

/-- Decompose v = ⟨e₀|v⟩·e₀ + v_orth with ‖e₀‖=1, v_orth ⟂ e₀. -/
lemma decompose_orthogonal_unit {ι : Type*} [Fintype ι]
    (e₀ v : EuclideanSpace ℂ ι) (h_norm : ‖e₀‖ = 1) :
    let c := inner ℂ e₀ v
    let v_orth := v - c • e₀
    inner ℂ e₀ v_orth = 0 ∧ ‖v‖ ^ 2 = Complex.normSq c + ‖v_orth‖ ^ 2 ∧ ‖v_orth‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  intro c v_orth
  have h_orth : inner ℂ e₀ v_orth = 0 := by
    change inner ℂ e₀ (v - c • e₀) = 0
    rw [inner_sub_right, inner_smul_right]
    have h_self : inner ℂ e₀ e₀ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, h_norm]
      norm_num
    change inner ℂ e₀ v - (inner ℂ e₀ v) * inner ℂ e₀ e₀ = 0
    rw [h_self]
    ring
  have h_norm_sq : ‖v‖ ^ 2 = Complex.normSq c + ‖v_orth‖ ^ 2 := by
    calc
      ‖v‖ ^ 2 = ‖c • e₀ + v_orth‖ ^ 2 := by
        change ‖v‖ ^ 2 = ‖c • e₀ + (v - c • e₀)‖ ^ 2
        have hv : c • e₀ + (v - c • e₀) = v := by
          rw [sub_eq_add_neg]
          abel
        rw [hv]
      _ = Complex.normSq c * ‖e₀‖ ^ 2 + ‖v_orth‖ ^ 2 :=
        norm_sq_smul_add_of_inner_eq_zero c e₀ v_orth h_orth
      _ = Complex.normSq c + ‖v_orth‖ ^ 2 := by rw [h_norm, one_pow, mul_one]
  have h_le : ‖v_orth‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h_norm_sq]; nlinarith [Complex.normSq_nonneg c]
  exact ⟨h_orth, h_norm_sq, h_le⟩

end

end QuantumAlg
