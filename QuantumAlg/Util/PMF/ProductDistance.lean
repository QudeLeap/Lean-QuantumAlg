/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Total variation under independent finite products

For normalized nonnegative finite weights, total variation of independent
products is bounded by the sum of their one-coordinate distances. The repeated
sample and scalar distinguishability consequences retain their explicit
probability and information-bound hypotheses. No measurement implementation
or physical statistical inequality is supplied by this module.
-/

@[expose] public section

namespace QuantumAlg.FiniteProductDistance

open scoped BigOperators

/-- Consequence of the preceding finite-distribution estimates. -/
noncomputable def TV {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |P x - Q x|

/-- Consequence of the preceding finite-distribution estimates. -/
def prodDist {α : Type*} (P : α → ℝ) (m : ℕ) : (Fin m → α) → ℝ :=
  fun f => ∏ i : Fin m, P (f i)

/-- |a*b - c*d| <= a*|b-d| + d*|a-c| for 0 <= a, 0 <= d. -/
lemma abs_mul_sub_mul_le {a b c d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    |a * b - c * d| ≤ a * |b - d| + d * |a - c| := by
  calc
    |a * b - c * d| = |(a * b - a * d) + (a * d - c * d)| := by ring_nf
    _ ≤ |a * b - a * d| + |a * d - c * d| := abs_add_le _ _
    _ = a * |b - d| + d * |a - c| := by
      have h1 : |a * b - a * d| = a * |b - d| := by
        rw [← mul_sub]
        rw [abs_mul, abs_of_nonneg ha]
      have h2 : |a * d - c * d| = d * |a - c| := by
        rw [← sub_mul]
        rw [abs_mul, mul_comm, abs_of_nonneg hd]
      rw [h1, h2]

lemma tv_nonneg {α : Type*} [Fintype α] (P Q : α → ℝ) : 0 ≤ TV P Q := by
  unfold TV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- `Fin (m+1) → α` is canonically `α × (Fin m → α)`. -/
def finSuccProdEquiv (α : Type*) (m : ℕ) : (Fin (m + 1) → α) ≃ (α × (Fin m → α)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [Fin.tail]
  right_inv p := by
    cases p with
    | mk x g =>
      ext <;> simp [Fin.tail]

lemma prodDist_tail {m : ℕ} {α : Type*} (P : α → ℝ) (f : Fin (m + 1) → α) :
    prodDist P (m + 1) f = P (f 0) * prodDist P m (Fin.tail f) := by
  simp [prodDist, Fin.prod_univ_succ, Fin.tail]

lemma prodDist_nonneg {α : Type*} (P : α → ℝ) (hP : ∀ x, 0 ≤ P x) (m : ℕ)
    (f : Fin m → α) : 0 ≤ prodDist P m f := by
  unfold prodDist
  exact Finset.prod_nonneg (fun i hi => hP (f i))

/-- Normalization: `sum f, prodDist P m f = (sum x, P x) ^ m`. -/
lemma sum_prodDist {α : Type*} [Fintype α] (P : α → ℝ) (m : ℕ) :
    ∑ f : Fin m → α, prodDist P m f = (∑ x : α, P x) ^ m := by
  induction m with
  | zero =>
      simp [prodDist]
  | succ m ih =>
      calc
        ∑ f : Fin (m + 1) → α, prodDist P (m + 1) f
            = ∑ f : Fin (m + 1) → α, P (f 0) * prodDist P m (Fin.tail f) := by
                apply Finset.sum_congr rfl
                intro f hf
                exact prodDist_tail P f
        _ = ∑ p : α × (Fin m → α), P p.1 * prodDist P m p.2 := by
                exact Fintype.sum_equiv (finSuccProdEquiv α m)
                  (fun f => P (f 0) * prodDist P m (Fin.tail f))
                  (fun p => P p.1 * prodDist P m p.2)
                  (by intro f; rfl)
        _ = ∑ x : α, ∑ g : Fin m → α, P x * prodDist P m g := by
                rw [Fintype.sum_prod_type]
        _ = ∑ x : α, P x * (∑ g : Fin m → α, prodDist P m g) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mul_sum]
        _ = (∑ x : α, P x) * ∑ g : Fin m → α, prodDist P m g := by
                rw [Finset.sum_mul]
        _ = (∑ x : α, P x) * (∑ x : α, P x) ^ m := by rw [ih]
        _ = (∑ x : α, P x) ^ (m + 1) := by ring

/-- Two-factor TV subadditivity for product distributions. -/
lemma tv_prod_le {α β : Type*} [Fintype α] [Fintype β]
    (P₁ Q₁ : α → ℝ) (P₂ Q₂ : β → ℝ)
    (hP₁_nn : ∀ x, 0 ≤ P₁ x) (hQ₂_nn : ∀ y, 0 ≤ Q₂ y)
    (hP₁_sum : ∑ x, P₁ x ≤ 1) (hQ₂_sum : ∑ y, Q₂ y ≤ 1) :
    TV (fun p : α × β => P₁ p.1 * P₂ p.2) (fun p : α × β => Q₁ p.1 * Q₂ p.2) ≤
      TV P₁ Q₁ + TV P₂ Q₂ := by
  unfold TV
  calc
    (1 / 2 : ℝ) * ∑ p : α × β, |P₁ p.1 * P₂ p.2 - Q₁ p.1 * Q₂ p.2|
        ≤ (1 / 2 : ℝ) * ∑ p : α × β,
            (P₁ p.1 * |P₂ p.2 - Q₂ p.2| + Q₂ p.2 * |P₁ p.1 - Q₁ p.1|) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (s := (Finset.univ : Finset (α × β)))
              (f := fun p : α × β => |P₁ p.1 * P₂ p.2 - Q₁ p.1 * Q₂ p.2|)
              (g := fun p : α × β => P₁ p.1 * |P₂ p.2 - Q₂ p.2| + Q₂ p.2 * |P₁ p.1 - Q₁ p.1|)
              (fun p hp => abs_mul_sub_mul_le (hP₁_nn p.1) (hQ₂_nn p.2)))
            (by norm_num)
    _ = (1 / 2 : ℝ) *
          ((∑ x : α, P₁ x) * (∑ y : β, |P₂ y - Q₂ y|) +
            (∑ x : α, |P₁ x - Q₁ x|) * (∑ y : β, Q₂ y)) := by
          congr 1
          calc
            ∑ p : α × β, (P₁ p.1 * |P₂ p.2 - Q₂ p.2| + Q₂ p.2 * |P₁ p.1 - Q₁ p.1|)
                = (∑ p : α × β, P₁ p.1 * |P₂ p.2 - Q₂ p.2|) +
                  (∑ p : α × β, Q₂ p.2 * |P₁ p.1 - Q₁ p.1|) := by
                  rw [Finset.sum_add_distrib]
            _ = (∑ x : α, P₁ x) * (∑ y : β, |P₂ y - Q₂ y|) +
                (∑ x : α, |P₁ x - Q₁ x|) * (∑ y : β, Q₂ y) := by
                  congr 1
                  · rw [Fintype.sum_prod_type]
                    rw [Fintype.sum_mul_sum]
                  · rw [Fintype.sum_prod_type]
                    rw [Fintype.sum_mul_sum]
                    apply Finset.sum_congr rfl
                    intro x hx
                    apply Finset.sum_congr rfl
                    intro y hy
                    rw [mul_comm]
    _ = (∑ x : α, P₁ x) * TV P₂ Q₂ + (∑ y : β, Q₂ y) * TV P₁ Q₁ := by
          unfold TV
          ring
    _ ≤ TV P₁ Q₁ + TV P₂ Q₂ := by
          have h1 : (∑ x : α, P₁ x) * TV P₂ Q₂ ≤ TV P₂ Q₂ :=
            mul_le_of_le_one_left (tv_nonneg P₂ Q₂) hP₁_sum
          have h2 : (∑ y : β, Q₂ y) * TV P₁ Q₁ ≤ TV P₁ Q₁ :=
            mul_le_of_le_one_left (tv_nonneg P₁ Q₁) hQ₂_sum
          linarith

/-- TV subadditivity for m independent samples. -/
lemma tv_prodDist_le {α : Type*} [Fintype α] (P Q : α → ℝ)
    (hP_nn : ∀ x, 0 ≤ P x) (hQ_nn : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    ∀ m : ℕ, TV (prodDist P m) (prodDist Q m) ≤ (m : ℝ) * TV P Q := by
  intro m
  induction m with
  | zero =>
      have hz : TV (prodDist P 0) (prodDist Q 0) = 0 := by
        simp [TV, prodDist]
      rw [hz]
      norm_num
  | succ m ih =>
      calc
        TV (prodDist P (m + 1)) (prodDist Q (m + 1))
            = TV (fun p : α × (Fin m → α) => P p.1 * prodDist P m p.2)
                 (fun p : α × (Fin m → α) => Q p.1 * prodDist Q m p.2) := by
                unfold TV
                congr 1
                exact Fintype.sum_equiv (finSuccProdEquiv α m)
                  (fun f => |prodDist P (m + 1) f - prodDist Q (m + 1) f|)
                  (fun p => |P p.1 * prodDist P m p.2 - Q p.1 * prodDist Q m p.2|)
                  (by intro f; simp [prodDist_tail, finSuccProdEquiv])
        _ ≤ TV P Q + TV (prodDist P m) (prodDist Q m) := by
                have hsQ : ∑ g : Fin m → α, prodDist Q m g ≤ 1 := by
                  have hs := sum_prodDist Q m
                  simp [hs, hQ_sum, one_pow]
                exact tv_prod_le P Q (prodDist P m) (prodDist Q m) hP_nn
                  (prodDist_nonneg Q hQ_nn m) (le_of_eq hP_sum) hsQ
        _ ≤ TV P Q + (m : ℝ) * TV P Q := by
                linarith [ih]
        _ = ((m : ℝ) + 1) * TV P Q := by ring
        _ = ((m + 1 : ℕ) : ℝ) * TV P Q := by
                rw [Nat.cast_add, Nat.cast_one]

/-- sqrt(4*(x/2)) style identity used by the TV-bound conjunct. -/
lemma two_mul_sqrt_half {x : ℝ} (hx : 0 ≤ x) : 2 * Real.sqrt (x / 2) = Real.sqrt (2 * x) := by
  have hmain : (2 * Real.sqrt (x / 2)) ^ 2 = 2 * x := by
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ x / 2)]
    ring_nf
  apply le_antisymm
  · rw [← hmain, Real.sqrt_sq_eq_abs]
    exact le_abs_self _
  · rw [← hmain, Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]

/-- Consequence of the preceding finite-distribution estimates. -/
theorem sampleCount_lower_bound {irreps : Type*} [Fintype irreps]
    (n : ℕ) (hn : 1 < n)
    (P_triv P_pi : irreps → ℝ)
    (hP_triv_nn : ∀ x, 0 ≤ P_triv x)
    (hP_triv_sum : ∑ x, P_triv x = 1)
    (hP_pi_nn : ∀ x, 0 ≤ P_pi x)
    (hP_pi_sum : ∑ x, P_pi x = 1)
    (conjCard : ℕ)
    (h_conj_card_exact : conjCard = Nat.choose n 2 ∧ conjCard = n * (n - 1) / 2)
    (h_weak_fourier_bound : TV P_triv P_pi ≤ 1 / (2 * Real.sqrt (conjCard : ℝ))) :
    conjCard = Nat.choose n 2 ∧
      conjCard = n * (n - 1) / 2 ∧
      TV P_triv P_pi ≤ 1 / Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) ∧
      (∀ m : ℕ, TV (prodDist P_triv m) (prodDist P_pi m) ≤ (m : ℝ) * TV P_triv P_pi) ∧
      (∀ advantage : ℝ, 0 < advantage → ∃ c : ℝ, 0 < c ∧
        ∀ m : ℕ, advantage ≤ TV (prodDist P_triv m) (prodDist P_pi m) → c * (n : ℝ) ≤ (m : ℝ)) := by
  have hn1 : (1 : ℕ) ≤ n := le_of_lt hn
  have hn2 : (2 : ℕ) ≤ n := Nat.succ_le_of_lt hn
  let x : ℝ := (n : ℝ) * ((n : ℝ) - 1)
  have hx0 : 0 ≤ x := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1r : 0 ≤ (n : ℝ) - 1 := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by
        rw [← Nat.cast_one]
        exact Nat.cast_le.mpr hn1
      linarith
    exact mul_nonneg hn0 hn1r
  have h2dvd : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k * (n - 1), ?_⟩
      rw [hk]
      ring
    · refine ⟨k * n, ?_⟩
      have hnsub : n - 1 = 2 * k := by
        rw [hk]
        exact Nat.add_sub_cancel (2 * k) 1
      rw [hnsub, hk]
      ring
  have hcast : (conjCard : ℝ) = x / 2 := by
    rw [h_conj_card_exact.2]
    rw [Nat.cast_div h2dvd (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    rw [Nat.cast_mul]
    congr 1
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        simpa [Nat.cast_add] using congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel hn1)
      linarith
    exact hsub
  have hsqrt : 2 * Real.sqrt (x / 2) = Real.sqrt (2 * x) := two_mul_sqrt_half hx0
  refine ⟨h_conj_card_exact.1, h_conj_card_exact.2, ?_, ?_, ?_⟩
  · -- single-sample TV bound
    calc
      TV P_triv P_pi ≤ 1 / (2 * Real.sqrt (conjCard : ℝ)) := h_weak_fourier_bound
      _ = 1 / Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
        rw [hcast, hsqrt]
        simp only [x, mul_assoc]
  · -- TV subadditivity
    exact tv_prodDist_le P_triv P_pi hP_triv_nn hP_pi_nn hP_triv_sum hP_pi_sum
  · -- Omega(n) sample count
    intro advantage hadv
    refine ⟨advantage, hadv, ?_⟩
    intro m hm
    have hsub := tv_prodDist_le P_triv P_pi hP_triv_nn hP_pi_nn hP_triv_sum hP_pi_sum m
    have hmul : (m : ℝ) * TV P_triv P_pi ≤ (m : ℝ) * (1 / (2 * Real.sqrt (conjCard : ℝ))) := by
      exact mul_le_mul_of_nonneg_left h_weak_fourier_bound (Nat.cast_nonneg m)
    have hchain : advantage ≤ (m : ℝ) * (1 / (2 * Real.sqrt (conjCard : ℝ))) :=
      le_trans (le_trans hm hsub) hmul
    have hle1 : advantage ≤ (m : ℝ) / (2 * Real.sqrt (conjCard : ℝ)) := by
      calc
        advantage ≤ (m : ℝ) * (1 / (2 * Real.sqrt (conjCard : ℝ))) := hchain
        _ = (m : ℝ) / (2 * Real.sqrt (conjCard : ℝ)) := by ring
    have hle2 : (m : ℝ) / (2 * Real.sqrt (conjCard : ℝ)) = (m : ℝ) / Real.sqrt (2 * x) := by
      rw [hcast, hsqrt]
    have hle3 : advantage ≤ (m : ℝ) / Real.sqrt (2 * x) := by
      rw [← hle2]
      exact hle1
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact Nat.cast_pos.mpr (lt_trans (by norm_num : 0 < 1) hn)
    have h2x0 : 0 ≤ 2 * x := by linarith
    have hns : (n : ℝ) ≤ Real.sqrt (2 * x) := by
      rw [Real.le_sqrt (Nat.cast_nonneg n) h2x0]
      have hpoly : 0 ≤ (n : ℝ) ^ 2 - 2 * (n : ℝ) := by
        have hn2r : (2 : ℝ) ≤ (n : ℝ) := by
          rw [← Nat.cast_two]
          exact Nat.cast_le.mpr hn2
        have hx1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith [hn2r]
        have hsq1 : (1 : ℝ) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := by
          have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hx1 2
          simpa using h
        have hring : ((n : ℝ) - 1) ^ 2 - 1 = (n : ℝ) ^ 2 - 2 * (n : ℝ) := by ring
        linarith [hsq1, hring]
      have h2x : (n : ℝ) ^ 2 ≤ 2 * x := by
        unfold x
        have hring : 2 * ((n : ℝ) * ((n : ℝ) - 1)) - (n : ℝ) ^ 2 =
            (n : ℝ) ^ 2 - 2 * (n : ℝ) := by ring
        linarith [hpoly, hring]
      exact h2x
    have hdiv : (m : ℝ) / Real.sqrt (2 * x) ≤ (m : ℝ) / (n : ℝ) := by
      have h1 : 1 / Real.sqrt (2 * x) ≤ 1 / (n : ℝ) :=
        one_div_le_one_div_of_le hn0 hns
      have hm : (m : ℝ) * (1 / Real.sqrt (2 * x)) ≤ (m : ℝ) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m)
      calc
        (m : ℝ) / Real.sqrt (2 * x) = (m : ℝ) * (1 / Real.sqrt (2 * x)) := by ring
        _ ≤ (m : ℝ) * (1 / (n : ℝ)) := hm
        _ = (m : ℝ) / (n : ℝ) := by ring
    have hle4 : advantage ≤ (m : ℝ) / (n : ℝ) := le_trans hle3 hdiv
    have hmuln : advantage * (n : ℝ) ≤ (m : ℝ) / (n : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hle4 (le_of_lt hn0)
    have hcancel : (m : ℝ) / (n : ℝ) * (n : ℝ) = (m : ℝ) := by
      field_simp [ne_of_gt hn0]
    calc
      advantage * (n : ℝ) ≤ (m : ℝ) / (n : ℝ) * (n : ℝ) := hmuln
      _ = (m : ℝ) := hcancel

end QuantumAlg.FiniteProductDistance
