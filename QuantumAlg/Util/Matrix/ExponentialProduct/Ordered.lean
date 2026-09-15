/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.Range
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite ordered-product defect propagation

An ordered product and the exponential of its partial sums are compared by an
exact telescoping recurrence. Explicit norm-like inequalities, exponential
growth, and local defect bounds give the accumulated estimate
`(C exp R / 2) M (M - 1) γ²` when `M γ ≤ R`. The local defect bound remains an
explicit hypothesis; this module establishes the finite-family propagation.
-/

@[expose] public section

namespace Matrix.ExponentialProduct.Ordered

open scoped BigOperators

/-- Definition: S_k = sum_{j=1}^k H_j. -/
def partialSum {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ j ∈ Finset.Icc 1 k, H j

/-- Definition: ordered product e^{H_1} ... e^{H_M}. -/
def orderedExpProduct {d : ℕ} (M : ℕ) (H : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((List.range M).map (fun i => expm (H (i + 1)))).prod

/-- Tail product expm (H_{k+1}) ... expm (H_M), empty when k = M. -/
def tailExp {d : ℕ} (M k : ℕ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((List.range (M - k)).map (fun i => expm (H (k + 1 + i)))).prod

private lemma orderedExpProduct_succ {d : ℕ} (M : ℕ) (H : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :
    orderedExpProduct (M + 1) H expm = orderedExpProduct M H expm * expm (H (M + 1)) := by
  unfold orderedExpProduct
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

private lemma tailExp_self {d : ℕ} (M : ℕ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℂ) :
    tailExp M M expm H = 1 := by
  simp [tailExp]

private lemma tailExp_succ {d : ℕ} (M k : ℕ) (hk : k ≤ M)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℂ) :
    tailExp (M + 1) k expm H = tailExp M k expm H * expm (H (M + 1)) := by
  unfold tailExp
  have hsub : M + 1 - k = (M - k) + 1 := by
    rw [← Nat.sub_add_comm hk]
  rw [hsub, List.range_succ, List.map_append, List.prod_append]
  have hindex : k + 1 + (M - k) = M + 1 := by
    rw [add_assoc, add_comm 1 (M - k), ← add_assoc, add_comm k (M - k), Nat.sub_add_cancel hk]
  simp [hindex]

/-- opnorm of a list product is at most the list product of opnorms. -/
private lemma opnorm_list_prod_le {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (h_one : opnorm 1 ≤ 1)
    (h_nonneg : ∀ A, 0 ≤ opnorm A)
    (h_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B)
    (l : List ℕ) (A : ℕ → Matrix (Fin d) (Fin d) ℂ) :
    opnorm ((l.map A).prod) ≤ (l.map (fun i => opnorm (A i))).prod := by
  induction l with
  | nil => simpa using h_one
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact le_trans (h_submul (A a) ((l.map A).prod))
        (mul_le_mul_of_nonneg_left ih (h_nonneg (A a)))

/-- opnorm of the ordered product over 1..j is at most the product of opnorms. -/
private lemma opnorm_orderedExpProduct_le {d : ℕ} (j : ℕ) (H : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (h_one : opnorm 1 ≤ 1)
    (h_nonneg : ∀ A, 0 ≤ opnorm A)
    (h_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B) :
    opnorm (orderedExpProduct j H expm) ≤
      ((List.range j).map (fun i => opnorm (expm (H (i + 1))))).prod := by
  unfold orderedExpProduct
  exact opnorm_list_prod_le opnorm h_one h_nonneg h_submul (List.range j)
    (fun i => expm (H (i + 1)))

/-- opnorm of the tail product is at most the product of the opnorms of its factors. -/
private lemma opnorm_tailExp_le {d : ℕ} (M k : ℕ)
    (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (h_one : opnorm 1 ≤ 1)
    (h_nonneg : ∀ A, 0 ≤ opnorm A)
    (h_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B) :
    opnorm (tailExp M k expm H) ≤
      ((List.range (M - k)).map (fun i => opnorm (expm (H (k + 1 + i))))).prod := by
  unfold tailExp
  exact opnorm_list_prod_le opnorm h_one h_nonneg h_submul (List.range (M - k))
    (fun i => expm (H (k + 1 + i)))

/-- exp is nondecreasing. -/
private lemma exp_mono {a b : ℝ} (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  exact Real.exp_le_exp.mpr h

/-- e^gamma raised to n is at most e^{n*gamma}. -/
private lemma exp_pow_le (γ : ℝ) (n : ℕ) : Real.exp γ ^ n ≤ Real.exp ((n : ℝ) * γ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      rw [Nat.cast_add, Nat.cast_one]
      rw [show (↑n + 1 : ℝ) * γ = (n : ℝ) * γ + γ by ring]
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right ih (Real.exp_pos γ).le

/-- product of e^gamma over n factors is e^{n*gamma}. -/
private lemma prod_exp_le {n : ℕ} (γ : ℝ) :
    ((List.range n).map (fun _ => Real.exp γ)).prod ≤ Real.exp ((n : ℝ) * γ) := by
  simpa [List.prod_replicate, List.length_range] using exp_pow_le γ n

/-- Norm bound of the partial sum S_k = sum_{j=1}^k H_j. -/
private lemma opnorm_partialSum_le {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_subadd : ∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B)
    (H : ℕ → Matrix (Fin d) (Fin d) ℂ) (k : ℕ) (γ : ℝ)
    (hH : ∀ j ∈ Finset.Icc 1 k, opnorm (H j) ≤ γ) :
    opnorm (partialSum H k) ≤ (k : ℝ) * γ := by
  unfold partialSum
  have hsum : opnorm (∑ j ∈ Finset.Icc 1 k, H j) ≤ ∑ j ∈ Finset.Icc 1 k, opnorm (H j) := by
    refine Finset.induction_on (Finset.Icc 1 k) ?_ ?_
    · simp [h_opnorm_zero]
    · intro a s has ih
      simp only [Finset.sum_insert has]
      exact le_trans (h_subadd (H a) (∑ x ∈ s, H x)) (by
        rw [add_comm (opnorm (H a)) (opnorm (∑ x ∈ s, H x)),
            add_comm (opnorm (H a)) (∑ x ∈ s, opnorm (H x))]
        exact add_le_add_left ih (opnorm (H a)))
  calc
    opnorm (∑ j ∈ Finset.Icc 1 k, H j) ≤ ∑ j ∈ Finset.Icc 1 k, opnorm (H j) := hsum
    _ ≤ ∑ j ∈ Finset.Icc 1 k, γ :=
      Finset.sum_le_sum (s := Finset.Icc 1 k) (f := fun j => opnorm (H j)) (g := fun _ => γ)
        (fun j hj => hH j hj)
    _ = (k : ℝ) * γ := by
      rw [Finset.sum_const]
      simp

/-- A product of nonnegative reals is nonnegative. -/
private lemma prod_nonneg {ι : Type*} (l : List ι) (f : ι → ℝ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (h0 a (by simp)) (ih (fun x hx => h0 x (by simp [hx])))

/-- Pointwise order on nonnegative lists extends to products. -/
private lemma prod_le_prod_of_le {ι : Type*} (l : List ι) (f g : ι → ℝ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_le_mul (h a (by simp))
        (ih (fun x hx => h0 x (by simp [hx])) (fun x hx => h x (by simp [hx])))
        (prod_nonneg l f (fun x hx => h0 x (by simp [hx])))
        (le_trans (h0 a (by simp)) (h a (by simp)))

/-- Norm of the tail product: each factor has norm at most e^gamma. -/
private lemma tailExp_norm_bound {d : ℕ} (M k : ℕ) (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (γ : ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (h_one : opnorm 1 ≤ 1)
    (h_nonneg : ∀ A, 0 ≤ opnorm A)
    (h_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B)
    (hk : k ≤ M)
    (hH : ∀ j ∈ Finset.Icc (k + 1) M, opnorm (H j) ≤ γ)
    (h_expm_bound : ∀ H, opnorm (expm H) ≤ Real.exp (opnorm H)) :
    opnorm (tailExp M k expm H) ≤ Real.exp (((M - k : ℕ) : ℝ) * γ) := by
  calc
    opnorm (tailExp M k expm H) ≤
        ((List.range (M - k)).map (fun i => opnorm (expm (H (k + 1 + i))))).prod :=
      opnorm_tailExp_le M k opnorm expm H h_one h_nonneg h_submul
    _ ≤ ((List.range (M - k)).map (fun _ => Real.exp γ)).prod := by
      apply prod_le_prod_of_le (List.range (M - k))
        (fun i => opnorm (expm (H (k + 1 + i)))) (fun _ => Real.exp γ)
      · intro i hi
        exact h_nonneg (expm (H (k + 1 + i)))
      · intro i hi
        have hxmem : k + 1 + i ∈ Finset.Icc (k + 1) M := by
          rw [Finset.mem_Icc]
          constructor
          · omega
          · have hi_lt : i < M - k := List.mem_range.mp hi
            omega
        exact le_trans (h_expm_bound (H (k + 1 + i))) (exp_mono (hH (k + 1 + i) hxmem))
    _ ≤ Real.exp (((M - k : ℕ) : ℝ) * γ) := prod_exp_le γ

/-- Norm bound of S_{k-1} for k in [1, M]. -/
private lemma opnorm_S_sub_one_le {d : ℕ} (M k : ℕ) (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℂ) (γ : ℝ)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_subadd : ∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B)
    (hk : k ∈ Finset.Icc 1 M)
    (hS : ∀ k ∈ Finset.Icc 1 M, S k = partialSum H k)
    (hS0 : S 0 = 0)
    (hH : ∀ j ∈ Finset.Icc 1 M, opnorm (H j) ≤ γ) :
    opnorm (S (k - 1)) ≤ ((k - 1 : ℕ) : ℝ) * γ := by
  by_cases hk1 : 1 ≤ k - 1
  · have hk_le_M : k ≤ M := (Finset.mem_Icc.mp hk).2
    have hkm : k - 1 ≤ M := by omega
    have hS' : S (k - 1) = partialSum H (k - 1) :=
      hS (k - 1) (Finset.mem_Icc.mpr ⟨hk1, hkm⟩)
    have hb := opnorm_partialSum_le opnorm h_opnorm_zero h_subadd H (k - 1) γ
      (fun j hj =>
        let ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        hH j (Finset.mem_Icc.mpr ⟨hj1, by omega⟩))
    rw [← hS'] at hb
    exact hb
  · have hk0 : k - 1 = 0 := by omega
    rw [hk0, hS0, h_opnorm_zero]
    simp

/-- Norm bound of the local remainder F_k. -/
private lemma F_norm_bound {d : ℕ} (M k : ℕ) (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (C γ : ℝ) (H F S : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_subadd : ∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B)
    (h_nonneg : ∀ A, 0 ≤ opnorm A)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hk : k ∈ Finset.Icc 1 M)
    (hS : ∀ k ∈ Finset.Icc 1 M, S k = partialSum H k)
    (hS0 : S 0 = 0)
    (hH : ∀ j ∈ Finset.Icc 1 M, opnorm (H j) ≤ γ)
    (hF : ∀ k ∈ Finset.Icc 1 M,
        opnorm (F k) ≤ C * opnorm (S (k - 1)) * opnorm (H k) * Real.exp (opnorm (S (k - 1)) +
          opnorm (H k))) :
    opnorm (F k) ≤ C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp ((k : ℝ) * γ) := by
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  let a : ℝ := opnorm (S (k - 1))
  let A : ℝ := ((k - 1 : ℕ) : ℝ) * γ
  let b : ℝ := opnorm (H k)
  let e : ℝ := Real.exp (a + b)
  let E : ℝ := Real.exp (A + γ)
  have hopS : a ≤ A := by
    dsimp [a, A]
    exact opnorm_S_sub_one_le M k opnorm H S γ h_opnorm_zero h_subadd hk hS hS0 hH
  have hHk : b ≤ γ := by
    dsimp [b]
    exact hH k hk
  have ha0 : 0 ≤ a := by dsimp [a]; exact h_nonneg (S (k - 1))
  have hb0 : 0 ≤ b := by dsimp [b]; exact h_nonneg (H k)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (k - 1))) hγ
  have he0 : 0 ≤ e := by dsimp [e]; exact Real.exp_nonneg (a + b)
  have hE0 : 0 ≤ E := by dsimp [E]; exact Real.exp_nonneg (A + γ)
  have hsum_le : a + b ≤ A + γ := by linarith
  have he_le : e ≤ E := by
    dsimp [e, E]
    exact exp_mono hsum_le
  have hCA0 : 0 ≤ C * A := mul_nonneg hC hA0
  have hCAγ0 : 0 ≤ C * A * γ := mul_nonneg hCA0 hγ
  calc
    opnorm (F k) ≤ C * a * b * e := by
      dsimp [a, b, e]
      exact hF k hk
    _ ≤ C * A * b * e := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hopS hC) hb0) he0
    _ ≤ C * A * γ * e := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHk hCA0) he0
    _ ≤ C * A * γ * E := by
      exact mul_le_mul_of_nonneg_left he_le hCAγ0
    _ = C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp ((k : ℝ) * γ) := by
      have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
        rw [Nat.cast_sub hk1]
        ring
      have hEexp : Real.exp (((k - 1 : ℕ) : ℝ) * γ + γ) = Real.exp ((k : ℝ) * γ) := by
        congr 1
        rw [show ((k - 1 : ℕ) : ℝ) * γ + γ = (((k - 1 : ℕ) : ℝ) + 1) * γ by ring]
        rw [hcast]
      dsimp [A, E]
      rw [hEexp]
      ring

/-- The global error recurrence: E_{j+1} = E_j * expm (H (j+1)) + F (j+1). -/
lemma error_rec_succ {d : ℕ} (j : ℕ) (H F : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (h_local_j : expm (S j) * expm (H (j + 1)) = expm (S (j + 1)) + F (j + 1)) :
    (orderedExpProduct (j + 1) H expm - expm (S (j + 1))) =
      (orderedExpProduct j H expm - expm (S j)) * expm (H (j + 1)) + F (j + 1) := by
  rw [orderedExpProduct_succ j H expm]
  have hC : expm (S (j + 1)) = expm (S j) * expm (H (j + 1)) - F (j + 1) := by
    rw [h_local_j]
    abel
  rw [hC]
  noncomm_ring

/-- Icc 1 (n+1) = insert (n+1) (Icc 1 n). -/
private lemma Icc_one_succ {n : ℕ} : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
  ext x
  rw [Finset.mem_insert]
  constructor
  · intro hx
    rcases Finset.mem_Icc.mp hx with ⟨h1, h2⟩
    by_cases h : x = n + 1
    · exact Or.inl h
    · exact Or.inr (Finset.mem_Icc.mpr ⟨h1, by
        have hxle : x ≤ n := by omega
        exact hxle⟩)
  · intro hx
    rcases hx with hx | hx
    · rw [hx]
      exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, by
        have hx2 : x ≤ n := (Finset.mem_Icc.mp hx).2
        omega⟩

/-- Unrolled error: E_j = sum_{k=1}^j F k * tailExp j k. -/
lemma error_unrolled {d : ℕ} (j : ℕ) (H F : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ k ∈ Finset.Icc 1 j, expm (S (k - 1)) * expm (H k) = expm (S k) + F k)
    (hS : ∀ k ∈ Finset.Icc 1 j, S k = partialSum H k)
    (hS0 : S 0 = 0) (he0 : expm 0 = 1) :
    orderedExpProduct j H expm - expm (S j) =
      ∑ k ∈ Finset.Icc 1 j, F k * tailExp j k expm H := by
  induction j with
  | zero => simp [orderedExpProduct, tailExp, hS0, he0]
  | succ j ih =>
      have hrec : expm (S j) * expm (H (j + 1)) = expm (S (j + 1)) + F (j + 1) :=
        hF (j + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      rw [error_rec_succ j H F S expm hrec]
      have hFj : ∀ k ∈ Finset.Icc 1 j, expm (S (k - 1)) * expm (H k) = expm (S k) + F k := by
        intro k hk
        exact hF k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
          le_trans (Finset.mem_Icc.mp hk).2 (Nat.le_succ j)⟩)
      have hSj : ∀ k ∈ Finset.Icc 1 j, S k = partialSum H k := by
        intro k hk
        exact hS k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
          le_trans (Finset.mem_Icc.mp hk).2 (Nat.le_succ j)⟩)
      rw [ih hFj hSj]
      rw [Finset.sum_mul]
      rw [Icc_one_succ, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
      rw [tailExp_self]
      rw [mul_one]
      rw [add_comm (F (j + 1)) (∑ k ∈ Finset.Icc 1 j, F k * tailExp (j + 1) k expm H)]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_assoc]
      rw [tailExp_succ j k (Finset.mem_Icc.mp hk).2 expm H]

/-- Norm bound of the unrolled error (the core estimate). -/
private lemma opnorm_error_unrolled_le {d : ℕ} (j : ℕ) (H F : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_subadd : ∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B)
    (h_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B)
    (hF : ∀ k ∈ Finset.Icc 1 j, expm (S (k - 1)) * expm (H k) = expm (S k) + F k)
    (hS : ∀ k ∈ Finset.Icc 1 j, S k = partialSum H k)
    (hS0 : S 0 = 0) (he0 : expm 0 = 1) :
    opnorm (orderedExpProduct j H expm - expm (S j)) ≤
      ∑ k ∈ Finset.Icc 1 j, opnorm (F k) * opnorm (tailExp j k expm H) := by
  rw [error_unrolled j H F S expm hF hS hS0 he0]
  have hsum : opnorm (∑ k ∈ Finset.Icc 1 j, F k * tailExp j k expm H) ≤
      ∑ k ∈ Finset.Icc 1 j, opnorm (F k * tailExp j k expm H) := by
    refine Finset.induction_on (Finset.Icc 1 j) ?_ ?_
    · simp [h_opnorm_zero]
    · intro a s has ih
      simp only [Finset.sum_insert has]
      exact le_trans (h_subadd (F a * tailExp j a expm H) (∑ x ∈ s, F x * tailExp j x expm H)) (by
        rw [add_comm (opnorm (F a * tailExp j a expm H)) (opnorm (∑ x ∈ s, F x * tailExp j x expm
          H)),
            add_comm (opnorm (F a * tailExp j a expm H)) (∑ k ∈ s, opnorm (F k * tailExp j k expm
              H))]
        exact add_le_add_left ih (opnorm (F a * tailExp j a expm H)))
  refine le_trans hsum ?_
  exact Finset.sum_le_sum (fun k hk => h_submul (F k) (tailExp j k expm H))

/-- sum_{k=1}^M (k-1) = M (M-1) / 2, as reals. -/
private lemma sum_sub_one_eq (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, ((k - 1 : ℕ) : ℝ)) = (M : ℝ) * ((M : ℝ) - 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Icc_one_succ, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
      rw [ih]
      simp [Nat.cast_add]
      ring_nf

/-- Accumulated finite-product error from exponential growth and local defect bounds. -/
theorem ordered_product_error_bound
    {d : ℕ}
    (M : ℕ)
    (H F : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (E : Matrix (Fin d) (Fin d) ℂ)
    (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_opnorm_nonneg : ∀ A, 0 ≤ opnorm A)
    (h_opnorm_subadd : ∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B)
    (h_opnorm_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B)
    (h_expm_zero : expm 0 = 1)
    (h_expm_bound : ∀ H, opnorm (expm H) ≤ Real.exp (opnorm H))
    (C γ R : ℝ)
    (h_C_nonneg : 0 ≤ C)
    (hγ : 0 ≤ γ)
    (h_bound_Mγ : (M : ℝ) * γ ≤ R)
    (h_H_small : ∀ j ∈ Finset.Icc 1 M, opnorm (H j) ≤ γ)
    (h_S_zero : S 0 = 0)
    (h_S : ∀ k ∈ Finset.Icc 1 M, S k = partialSum H k)
    (h_local : ∀ k ∈ Finset.Icc 1 M,
        expm (S (k - 1)) * expm (H k) = expm (S k) + F k ∧
        opnorm (F k) ≤
          C * opnorm (S (k - 1)) * opnorm (H k) *
            Real.exp (opnorm (S (k - 1)) + opnorm (H k)))
    (h_error : orderedExpProduct M H expm = expm (S M) + E) :
    opnorm E ≤ (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 ∧
      ∃ K : ℝ, 0 ≤ K ∧ opnorm E ≤ K * (M : ℝ) ^ 2 * γ ^ 2 := by
  have h_one : opnorm 1 ≤ 1 := by
    have hb := h_expm_bound 0
    rwa [h_expm_zero, h_opnorm_zero, Real.exp_zero] at hb
  have hγ0 : 0 ≤ γ := hγ
  have hE : E = orderedExpProduct M H expm - expm (S M) := by
    rw [h_error]
    abel
  have herr : opnorm (orderedExpProduct M H expm - expm (S M)) ≤
      ∑ k ∈ Finset.Icc 1 M, opnorm (F k) * opnorm (tailExp M k expm H) := by
    exact opnorm_error_unrolled_le M H F S opnorm expm h_opnorm_zero h_opnorm_subadd h_opnorm_submul
      (fun k hk => (h_local k hk).1) (fun k hk => h_S k hk) h_S_zero h_expm_zero
  have hsummand : ∀ k ∈ Finset.Icc 1 M,
      opnorm (F k) * opnorm (tailExp M k expm H) ≤ C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp R := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_le_M : k ≤ M := (Finset.mem_Icc.mp hk).2
    have hFk := F_norm_bound M k opnorm C γ H F S h_opnorm_zero h_opnorm_subadd h_opnorm_nonneg
      h_C_nonneg hγ0 hk h_S h_S_zero h_H_small (fun k hk => (h_local k hk).2)
    have htail := tailExp_norm_bound M k opnorm γ H expm h_one h_opnorm_nonneg h_opnorm_submul
      hk_le_M
      (fun j hj =>
        let ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        h_H_small j (Finset.mem_Icc.mpr ⟨by omega, hj2⟩))
      h_expm_bound
    have htail0 : 0 ≤ opnorm (tailExp M k expm H) := h_opnorm_nonneg (tailExp M k expm H)
    have hkA0 : 0 ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (k - 1))
    have hA0 : 0 ≤ C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp ((k : ℝ) * γ) :=
      mul_nonneg (mul_nonneg (mul_nonneg h_C_nonneg hkA0) (sq_nonneg γ))
        (Real.exp_nonneg ((k : ℝ) * γ))
    have hexp : Real.exp ((k : ℝ) * γ) * Real.exp (((M - k : ℕ) : ℝ) * γ) = Real.exp ((M : ℝ) * γ)
      := by
      rw [← Real.exp_add]
      congr 1
      rw [← add_mul]
      congr 1
      rw [Nat.cast_sub hk_le_M]
      ring
    have hexp_le : Real.exp ((M : ℝ) * γ) ≤ Real.exp R := exp_mono h_bound_Mγ
    calc
      opnorm (F k) * opnorm (tailExp M k expm H)
          ≤ (C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp ((k : ℝ) * γ)) * opnorm (tailExp M k expm H)
            :=
            mul_le_mul_of_nonneg_right hFk htail0
      _ ≤ (C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp ((k : ℝ) * γ)) * Real.exp (((M - k : ℕ) : ℝ) *
        γ) :=
            mul_le_mul_of_nonneg_left htail hA0
      _ = C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * (Real.exp ((k : ℝ) * γ) * Real.exp (((M - k : ℕ) : ℝ) *
        γ)) := by ring
      _ = C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp ((M : ℝ) * γ) := by rw [hexp]
      _ ≤ C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp R :=
            mul_le_mul_of_nonneg_left hexp_le
              (mul_nonneg (mul_nonneg h_C_nonneg hkA0) (sq_nonneg γ))
  have hsum : (∑ k ∈ Finset.Icc 1 M, C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp R) =
      (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 := by
    calc
      (∑ k ∈ Finset.Icc 1 M, C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp R)
          = ∑ k ∈ Finset.Icc 1 M, (C * Real.exp R * γ ^ 2) * ((k - 1 : ℕ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (C * Real.exp R * γ ^ 2) * (∑ k ∈ Finset.Icc 1 M, ((k - 1 : ℕ) : ℝ)) := by
              rw [Finset.mul_sum]
      _ = (C * Real.exp R * γ ^ 2) * ((M : ℝ) * ((M : ℝ) - 1) / 2) := by rw [sum_sub_one_eq M]
      _ = (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 := by ring_nf
  have hbound : opnorm E ≤ (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 := by
    rw [hE]
    calc
      opnorm (orderedExpProduct M H expm - expm (S M)) ≤
          ∑ k ∈ Finset.Icc 1 M, opnorm (F k) * opnorm (tailExp M k expm H) := herr
      _ ≤ ∑ k ∈ Finset.Icc 1 M, C * ((k - 1 : ℕ) : ℝ) * γ ^ 2 * Real.exp R :=
            Finset.sum_le_sum hsummand
      _ = (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 := hsum
  constructor
  · exact hbound
  · refine ⟨C * Real.exp R / 2, ?_, ?_⟩
    · exact mul_nonneg (mul_nonneg h_C_nonneg (Real.exp_pos R).le) (by norm_num)
    · rw [hE]
      calc
        opnorm (orderedExpProduct M H expm - expm (S M)) ≤
            (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 :=
              le_trans herr (le_trans (Finset.sum_le_sum hsummand) (le_of_eq hsum))
        _ ≤ (C * Real.exp R / 2) * (M : ℝ) ^ 2 * γ ^ 2 := by
          have hK : 0 ≤ C * Real.exp R / 2 :=
            mul_nonneg (mul_nonneg h_C_nonneg (Real.exp_pos R).le) (by norm_num)
          have hM : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
          have hMsub : (M : ℝ) - 1 ≤ (M : ℝ) := by linarith
          have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
          have hstep : (M : ℝ) * ((M : ℝ) - 1) ≤ (M : ℝ) ^ 2 := by
            calc
              (M : ℝ) * ((M : ℝ) - 1) ≤ (M : ℝ) * (M : ℝ) :=
                mul_le_mul_of_nonneg_left hMsub hM
              _ = (M : ℝ) ^ 2 := by ring
          calc
            (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2
                = (C * Real.exp R / 2) * ((M : ℝ) * ((M : ℝ) - 1)) * γ ^ 2 := by ring
            _ ≤ (C * Real.exp R / 2) * (M : ℝ) ^ 2 * γ ^ 2 :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hK) hγ2

end Matrix.ExponentialProduct.Ordered
