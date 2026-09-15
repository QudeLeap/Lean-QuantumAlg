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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Leading commutator and cubic product remainder

A supplied second-order expansion for an exponential-like map determines the
leading commutator in the product defect. The norm-like functional's algebraic
inequalities and the three Taylor remainder bounds are explicit hypotheses.
The coefficient is `13 B + B² + 5/4` for inputs bounded by `0 ≤ γ ≤ 1`.
This theorem propagates the supplied remainder bounds; it is not a construction
of those bounds for an arbitrary exponential-like map.
-/

@[expose] public section

namespace Matrix.ExponentialProduct.CommutatorRemainder

open scoped BigOperators

/-- Definition: productDefect = e^{H1} e^{H2} - e^{H1+H2}. -/
def productDefect {d : ℕ} (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H1 H2 : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  expm H1 * expm H2 - expm (H1 + H2)

/-- `opnorm (-X) <= opnorm X` follows from scalar sub-homogeneity with a = -1. -/
private lemma opnorm_neg_le {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (h_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (X : Matrix (Fin d) (Fin d) ℂ) : opnorm (-X) ≤ opnorm X := by
  have h := h_scalar (-1 : ℂ) X
  simpa using h

/-- Expansion of the second-order product `(1 + H1 + (1/2) H1^2)(1 + H2 + (1/2) H2^2)`. -/
private lemma poly_expand {d : ℕ} (H1 H2 : Matrix (Fin d) (Fin d) ℂ) :
    (1 + H1 + (1 / 2 : ℂ) • (H1 * H1)) * (1 + H2 + (1 / 2 : ℂ) • (H2 * H2)) =
      1 + H1 + H2 + (1 / 2 : ℂ) • (H1 * H1) + (1 / 2 : ℂ) • (H2 * H2) + H1 * H2 +
        (1 / 2 : ℂ) • (H1 * H1 * H2) + (1 / 2 : ℂ) • (H1 * H2 * H2) +
        (1 / 4 : ℂ) • (H1 * H1 * H2 * H2) := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul]
  rw [smul_smul]
  norm_num
  simp_rw [← mul_assoc]
  abel_nf

/-- `(-2) • ((1/2) • X) = -X` (zsmul nested with a complex scalar). -/
private lemma neg_two_half {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    (-2 : ℤ) • ((1 / 2 : ℂ) • X) = -X := by
  rw [neg_zsmul]
  rw [show (2 : ℤ) • ((1 / 2 : ℂ) • X) = X by
    calc
      (2 : ℤ) • ((1 / 2 : ℂ) • X) = ((1 / 2 : ℂ) • X) + ((1 / 2 : ℂ) • X) := two_zsmul ((1 / 2 :
        ℂ) • X)
      _ = X := by
        rw [← add_smul]
        norm_num]

/-- Quadratic terms cancel exactly; only the third-order terms remain. -/
private lemma poly_identity {d : ℕ} (H1 H2 : Matrix (Fin d) (Fin d) ℂ) :
    (1 + H1 + (1 / 2 : ℂ) • (H1 * H1)) * (1 + H2 + (1 / 2 : ℂ) • (H2 * H2)) -
      (1 / 2 : ℂ) • (H1 * H2 - H2 * H1) -
      (1 + H1 + H2 + (1 / 2 : ℂ) • ((H1 + H2) * (H1 + H2))) =
      (1 / 2 : ℂ) • (H1 * H2 * H2) + (1 / 2 : ℂ) • (H1 * H1 * H2) +
        (1 / 4 : ℂ) • (H1 * H1 * H2 * H2) := by
  rw [poly_expand]
  have hsq : (H1 + H2) * (H1 + H2) = H1 * H1 + H1 * H2 + H2 * H1 + H2 * H2 := by
    noncomm_ring
  rw [hsq, smul_add, smul_add, smul_add]
  rw [smul_sub]
  simp_rw [sub_eq_add_neg, neg_add]
  abel_nf
  rw [neg_two_half (H1 * H2)]
  abel

/-- Error decomposition: the global error is the third-order terms plus
remainders, with the quadratic part cancelling by `poly_identity`. -/
private lemma error_decomp {d : ℕ} (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H1 H2 : Matrix (Fin d) (Fin d) ℂ) :
    productDefect expm H1 H2 - (1 / 2 : ℂ) • (H1 * H2 - H2 * H1) =
      (expm H1 - (1 + H1 + (1 / 2 : ℂ) • (H1 * H1))) *
          (1 + H2 + (1 / 2 : ℂ) • (H2 * H2)) +
        (1 + H1 + (1 / 2 : ℂ) • (H1 * H1)) *
          (expm H2 - (1 + H2 + (1 / 2 : ℂ) • (H2 * H2))) +
        (expm H1 - (1 + H1 + (1 / 2 : ℂ) • (H1 * H1))) *
          (expm H2 - (1 + H2 + (1 / 2 : ℂ) • (H2 * H2))) +
        ((1 / 2 : ℂ) • (H1 * H2 * H2) + (1 / 2 : ℂ) • (H1 * H1 * H2) +
          (1 / 4 : ℂ) • (H1 * H1 * H2 * H2)) -
        (expm (H1 + H2) - (1 + H1 + H2 + (1 / 2 : ℂ) • ((H1 + H2) * (H1 + H2)))) := by
  let E1 : Matrix (Fin d) (Fin d) ℂ := 1 + H1 + (1 / 2 : ℂ) • (H1 * H1)
  let E2 : Matrix (Fin d) (Fin d) ℂ := 1 + H2 + (1 / 2 : ℂ) • (H2 * H2)
  let productDefect' : Matrix (Fin d) (Fin d) ℂ :=
    1 + H1 + H2 + (1 / 2 : ℂ) • ((H1 + H2) * (H1 + H2))
  let R1 : Matrix (Fin d) (Fin d) ℂ := expm H1 - E1
  let R2 : Matrix (Fin d) (Fin d) ℂ := expm H2 - E2
  let R12 : Matrix (Fin d) (Fin d) ℂ := expm (H1 + H2) - productDefect'
  have he1 : expm H1 = E1 + R1 := by dsimp [R1]; abel
  have he2 : expm H2 = E2 + R2 := by dsimp [R2]; abel
  have he12 : expm (H1 + H2) = productDefect' + R12 := by dsimp [R12]; abel
  unfold productDefect
  rw [he1, he2, he12]
  have hdec : (E1 + R1) * (E2 + R2) - (productDefect' + R12) - (1 / 2 : ℂ) • (H1 * H2 - H2 * H1) =
      R1 * E2 + E1 * R2 + R1 * R2 +
        (E1 * E2 - (1 / 2 : ℂ) • (H1 * H2 - H2 * H1) - productDefect') - R12 := by
    noncomm_ring
  rw [hdec]
  dsimp [R1, R2, R12, E1, E2, productDefect']
  rw [poly_identity]
  noncomm_ring

/-- Local third-order bound of the error. -/
lemma commutator_remainder_bound {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (H1 H2 : Matrix (Fin d) (Fin d) ℂ) (B γ : ℝ)
    (h_nonneg : ∀ X, 0 ≤ opnorm X)
    (h_subadd : ∀ X Y, opnorm (X + Y) ≤ opnorm X + opnorm Y)
    (h_submul : ∀ X Y, opnorm (X * Y) ≤ opnorm X * opnorm Y)
    (h_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (h_one : opnorm 1 ≤ 1)
    (hB0 : 0 ≤ B) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hH1 : opnorm H1 ≤ γ) (hH2 : opnorm H2 ≤ γ)
    (hH12 : opnorm (H1 + H2) ≤ 2 * γ)
    (hR1 : opnorm (expm H1 - (1 + H1 + (1 / 2 : ℂ) • (H1 * H1))) ≤ B * opnorm H1 ^ 3)
    (hR2 : opnorm (expm H2 - (1 + H2 + (1 / 2 : ℂ) • (H2 * H2))) ≤ B * opnorm H2 ^ 3)
    (hR12 : opnorm (expm (H1 + H2) -
        (1 + H1 + H2 + (1 / 2 : ℂ) • ((H1 + H2) * (H1 + H2)))) ≤ B * opnorm (H1 + H2) ^ 3) :
    opnorm (productDefect expm H1 H2 - (1 / 2 : ℂ) • (H1 * H2 - H2 * H1)) ≤
      (13 * B + B ^ 2 + 5 / 4) * γ ^ 3 := by
  rw [error_decomp]
  let R1 : Matrix (Fin d) (Fin d) ℂ := expm H1 - (1 + H1 + (1 / 2 : ℂ) • (H1 * H1))
  let R2 : Matrix (Fin d) (Fin d) ℂ := expm H2 - (1 + H2 + (1 / 2 : ℂ) • (H2 * H2))
  let E1 : Matrix (Fin d) (Fin d) ℂ := 1 + H1 + (1 / 2 : ℂ) • (H1 * H1)
  let E2 : Matrix (Fin d) (Fin d) ℂ := 1 + H2 + (1 / 2 : ℂ) • (H2 * H2)
  let R12 : Matrix (Fin d) (Fin d) ℂ := expm (H1 + H2) -
    (1 + H1 + H2 + (1 / 2 : ℂ) • ((H1 + H2) * (H1 + H2)))
  let T : Matrix (Fin d) (Fin d) ℂ :=
    (1 / 2 : ℂ) • (H1 * H2 * H2) + (1 / 2 : ℂ) • (H1 * H1 * H2) +
      (1 / 4 : ℂ) • (H1 * H1 * H2 * H2)
  change opnorm (R1 * E2 + E1 * R2 + R1 * R2 + T - R12) ≤ (13 * B + B ^ 2 + 5 / 4) * γ ^ 3
  have hq2 : opnorm ((1 / 2 : ℂ) • (H2 * H2)) ≤ 1 / 2 * γ ^ 2 := by
    calc
      opnorm ((1 / 2 : ℂ) • (H2 * H2)) ≤ ‖(1 / 2 : ℂ)‖ * opnorm (H2 * H2) := h_scalar (1 / 2 : ℂ)
        (H2 * H2)
      _ = 1 / 2 * opnorm (H2 * H2) := by norm_num
      _ ≤ 1 / 2 * γ ^ 2 := by
        exact mul_le_mul_of_nonneg_left (le_trans (h_submul H2 H2)
          (by
            calc
              opnorm H2 * opnorm H2 ≤ γ * γ := mul_le_mul hH2 hH2 (h_nonneg H2) (le_trans
                (h_nonneg H2) hH2)
              _ = γ ^ 2 := by ring)) (by norm_num)
  have hE2 : opnorm E2 ≤ 5 / 2 := by
    dsimp [E2]
    calc
      opnorm (1 + H2 + (1 / 2 : ℂ) • (H2 * H2))
          ≤ opnorm (1 + H2) + opnorm ((1 / 2 : ℂ) • (H2 * H2)) :=
            h_subadd (1 + H2) ((1 / 2 : ℂ) • (H2 * H2))
      _ ≤ (opnorm 1 + opnorm H2) + opnorm ((1 / 2 : ℂ) • (H2 * H2)) :=
            add_le_add_left (h_subadd 1 H2) (opnorm ((1 / 2 : ℂ) • (H2 * H2)))
      _ ≤ 1 + γ + 1 / 2 * γ ^ 2 := by
            exact add_le_add (add_le_add h_one hH2) hq2
      _ ≤ 5 / 2 := by nlinarith [hγ0, hγ1]
  have hq1 : opnorm ((1 / 2 : ℂ) • (H1 * H1)) ≤ 1 / 2 * γ ^ 2 := by
    calc
      opnorm ((1 / 2 : ℂ) • (H1 * H1)) ≤ ‖(1 / 2 : ℂ)‖ * opnorm (H1 * H1) := h_scalar (1 / 2 : ℂ)
        (H1 * H1)
      _ = 1 / 2 * opnorm (H1 * H1) := by norm_num
      _ ≤ 1 / 2 * γ ^ 2 := by
        exact mul_le_mul_of_nonneg_left (le_trans (h_submul H1 H1)
          (by
            calc
              opnorm H1 * opnorm H1 ≤ γ * γ := mul_le_mul hH1 hH1 (h_nonneg H1) (le_trans
                (h_nonneg H1) hH1)
              _ = γ ^ 2 := by ring)) (by norm_num)
  have hE1 : opnorm E1 ≤ 5 / 2 := by
    dsimp [E1]
    calc
      opnorm (1 + H1 + (1 / 2 : ℂ) • (H1 * H1))
          ≤ opnorm (1 + H1) + opnorm ((1 / 2 : ℂ) • (H1 * H1)) :=
            h_subadd (1 + H1) ((1 / 2 : ℂ) • (H1 * H1))
      _ ≤ (opnorm 1 + opnorm H1) + opnorm ((1 / 2 : ℂ) • (H1 * H1)) :=
            add_le_add_left (h_subadd 1 H1) (opnorm ((1 / 2 : ℂ) • (H1 * H1)))
      _ ≤ 1 + γ + 1 / 2 * γ ^ 2 := by
            exact add_le_add (add_le_add h_one hH1) hq1
      _ ≤ 5 / 2 := by nlinarith [hγ0, hγ1]
  have hR1b : opnorm R1 ≤ B * γ ^ 3 := by
    dsimp [R1, E1]
    exact le_trans hR1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h_nonneg H1) hH1 3) hB0)
  have hR2b : opnorm R2 ≤ B * γ ^ 3 := by
    dsimp [R2, E2]
    exact le_trans hR2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h_nonneg H2) hH2 3) hB0)
  have hR12b : opnorm R12 ≤ 8 * B * γ ^ 3 := by
    dsimp [R12]
    calc
      opnorm (expm (H1 + H2) - (1 + H1 + H2 + (1 / 2 : ℂ) • ((H1 + H2) * (H1 + H2))))
          ≤ B * opnorm (H1 + H2) ^ 3 := hR12
      _ ≤ B * (2 * γ) ^ 3 := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h_nonneg (H1 + H2)) hH12 3) hB0
      _ = 8 * B * γ ^ 3 := by ring
  have htriple : opnorm (H1 * H2 * H2) ≤ γ ^ 3 := by
    calc
      opnorm (H1 * H2 * H2) ≤ opnorm (H1 * H2) * opnorm H2 := h_submul (H1 * H2) H2
      _ ≤ (opnorm H1 * opnorm H2) * opnorm H2 :=
        mul_le_mul_of_nonneg_right (h_submul H1 H2) (h_nonneg H2)
      _ ≤ γ * γ * γ := by
        calc
          (opnorm H1 * opnorm H2) * opnorm H2 ≤ (γ * γ) * opnorm H2 := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul hH1 hH2 (h_nonneg H2) (le_trans (h_nonneg
              H1) hH1)) (h_nonneg H2)
          _ ≤ (γ * γ) * γ := mul_le_mul_of_nonneg_left hH2 (mul_nonneg hγ0 hγ0)
      _ = γ ^ 3 := by ring
  have htriple2 : opnorm (H1 * H1 * H2) ≤ γ ^ 3 := by
    calc
      opnorm (H1 * H1 * H2) ≤ opnorm (H1 * H1) * opnorm H2 := h_submul (H1 * H1) H2
      _ ≤ (opnorm H1 * opnorm H1) * opnorm H2 :=
        mul_le_mul_of_nonneg_right (h_submul H1 H1) (h_nonneg H2)
      _ ≤ γ * γ * γ := by
        calc
          (opnorm H1 * opnorm H1) * opnorm H2 ≤ (γ * γ) * opnorm H2 := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul hH1 hH1 (h_nonneg H1) (le_trans (h_nonneg
              H1) hH1)) (h_nonneg H2)
          _ ≤ (γ * γ) * γ := mul_le_mul_of_nonneg_left hH2 (mul_nonneg hγ0 hγ0)
      _ = γ ^ 3 := by ring
  have hquad : opnorm (H1 * H1 * H2 * H2) ≤ γ ^ 3 := by
    calc
      opnorm (H1 * H1 * H2 * H2) ≤ opnorm (H1 * H1 * H2) * opnorm H2 := h_submul (H1 * H1 * H2) H2
      _ ≤ γ ^ 3 * opnorm H2 := mul_le_mul_of_nonneg_right htriple2 (h_nonneg H2)
      _ ≤ γ ^ 3 * γ := mul_le_mul_of_nonneg_left hH2 (by exact pow_nonneg hγ0 3)
      _ ≤ γ ^ 3 * 1 := mul_le_mul_of_nonneg_left hγ1 (by exact pow_nonneg hγ0 3)
      _ = γ ^ 3 := by ring
  have ht1 : opnorm ((1 / 2 : ℂ) • (H1 * H2 * H2)) ≤ 1 / 2 * γ ^ 3 := by
    calc
      opnorm ((1 / 2 : ℂ) • (H1 * H2 * H2)) ≤ ‖(1 / 2 : ℂ)‖ * opnorm (H1 * H2 * H2) :=
        h_scalar (1 / 2 : ℂ) (H1 * H2 * H2)
      _ = 1 / 2 * opnorm (H1 * H2 * H2) := by norm_num
      _ ≤ 1 / 2 * γ ^ 3 := mul_le_mul_of_nonneg_left htriple (by norm_num)
  have ht2 : opnorm ((1 / 2 : ℂ) • (H1 * H1 * H2)) ≤ 1 / 2 * γ ^ 3 := by
    calc
      opnorm ((1 / 2 : ℂ) • (H1 * H1 * H2)) ≤ ‖(1 / 2 : ℂ)‖ * opnorm (H1 * H1 * H2) :=
        h_scalar (1 / 2 : ℂ) (H1 * H1 * H2)
      _ = 1 / 2 * opnorm (H1 * H1 * H2) := by norm_num
      _ ≤ 1 / 2 * γ ^ 3 := mul_le_mul_of_nonneg_left htriple2 (by norm_num)
  have ht3 : opnorm ((1 / 4 : ℂ) • (H1 * H1 * H2 * H2)) ≤ 1 / 4 * γ ^ 3 := by
    calc
      opnorm ((1 / 4 : ℂ) • (H1 * H1 * H2 * H2)) ≤ ‖(1 / 4 : ℂ)‖ * opnorm (H1 * H1 * H2 * H2) :=
        h_scalar (1 / 4 : ℂ) (H1 * H1 * H2 * H2)
      _ = 1 / 4 * opnorm (H1 * H1 * H2 * H2) := by norm_num
      _ ≤ 1 / 4 * γ ^ 3 := mul_le_mul_of_nonneg_left hquad (by norm_num)
  have hT : opnorm T ≤ 5 / 4 * γ ^ 3 := by
    dsimp [T]
    calc
      opnorm ((1 / 2 : ℂ) • (H1 * H2 * H2) + (1 / 2 : ℂ) • (H1 * H1 * H2) +
          (1 / 4 : ℂ) • (H1 * H1 * H2 * H2))
          ≤ opnorm ((1 / 2 : ℂ) • (H1 * H2 * H2) + (1 / 2 : ℂ) • (H1 * H1 * H2)) +
              opnorm ((1 / 4 : ℂ) • (H1 * H1 * H2 * H2)) :=
            h_subadd ((1 / 2 : ℂ) • (H1 * H2 * H2) + (1 / 2 : ℂ) • (H1 * H1 * H2))
              ((1 / 4 : ℂ) • (H1 * H1 * H2 * H2))
      _ ≤ (opnorm ((1 / 2 : ℂ) • (H1 * H2 * H2)) + opnorm ((1 / 2 : ℂ) • (H1 * H1 * H2))) +
              opnorm ((1 / 4 : ℂ) • (H1 * H1 * H2 * H2)) :=
            add_le_add_left (h_subadd ((1 / 2 : ℂ) • (H1 * H2 * H2)) ((1 / 2 : ℂ) • (H1 * H1 * H2)))
              (opnorm ((1 / 4 : ℂ) • (H1 * H1 * H2 * H2)))
      _ ≤ (1 / 2 * γ ^ 3 + 1 / 2 * γ ^ 3) + 1 / 4 * γ ^ 3 :=
            add_le_add (add_le_add ht1 ht2) ht3
      _ = 5 / 4 * γ ^ 3 := by ring
  have hR1E2 : opnorm (R1 * E2) ≤ 5 / 2 * B * γ ^ 3 := by
    calc
      opnorm (R1 * E2) ≤ opnorm R1 * opnorm E2 := h_submul R1 E2
      _ ≤ (B * γ ^ 3) * (5 / 2) := mul_le_mul hR1b hE2 (h_nonneg E2) (le_trans (h_nonneg R1) hR1b)
      _ = 5 / 2 * B * γ ^ 3 := by ring
  have hE1R2 : opnorm (E1 * R2) ≤ 5 / 2 * B * γ ^ 3 := by
    calc
      opnorm (E1 * R2) ≤ opnorm E1 * opnorm R2 := h_submul E1 R2
      _ ≤ (5 / 2) * (B * γ ^ 3) := mul_le_mul hE1 hR2b (h_nonneg R2) (le_trans (h_nonneg E1) hE1)
      _ = 5 / 2 * B * γ ^ 3 := by ring
  have hR1R2 : opnorm (R1 * R2) ≤ B ^ 2 * γ ^ 3 := by
    calc
      opnorm (R1 * R2) ≤ B ^ 2 * γ ^ 6 := by
        calc
          opnorm (R1 * R2) ≤ opnorm R1 * opnorm R2 := h_submul R1 R2
          _ ≤ (B * γ ^ 3) * (B * γ ^ 3) := mul_le_mul hR1b hR2b (h_nonneg R2) (le_trans (h_nonneg
            R1) hR1b)
          _ = B ^ 2 * γ ^ 6 := by ring
      _ ≤ B ^ 2 * γ ^ 3 := by
        have hg6 : γ ^ 6 ≤ γ ^ 3 := by
          calc
            γ ^ 6 = γ ^ 3 * γ ^ 3 := by ring
            _ ≤ γ ^ 3 * 1 := mul_le_mul_of_nonneg_left (by simpa using (pow_le_pow_left₀ hγ0 hγ1
              3)) (by exact pow_nonneg hγ0 3)
            _ = γ ^ 3 := by ring
        exact mul_le_mul_of_nonneg_left hg6 (sq_nonneg B)
  have hsub3 : opnorm (R1 * E2 + E1 * R2 + R1 * R2) ≤ opnorm (R1 * E2) + opnorm (E1 * R2) + opnorm
    (R1 * R2) := by
    calc
      opnorm (R1 * E2 + E1 * R2 + R1 * R2) ≤ opnorm (R1 * E2 + E1 * R2) + opnorm (R1 * R2) :=
        h_subadd (R1 * E2 + E1 * R2) (R1 * R2)
      _ ≤ (opnorm (R1 * E2) + opnorm (E1 * R2)) + opnorm (R1 * R2) :=
        add_le_add_left (h_subadd (R1 * E2) (E1 * R2)) (opnorm (R1 * R2))
  have hsubT : opnorm (T - R12) ≤ opnorm T + opnorm R12 := by
    calc
      opnorm (T - R12) ≤ opnorm T + opnorm (-R12) := by
        simpa [sub_eq_add_neg] using h_subadd T (-R12)
      _ ≤ opnorm T + opnorm R12 := add_le_add_right (opnorm_neg_le opnorm h_scalar R12) (opnorm T)
  have hsum : opnorm (R1 * E2 + E1 * R2 + R1 * R2 + T - R12) ≤
      opnorm (R1 * E2) + opnorm (E1 * R2) + opnorm (R1 * R2) + opnorm T + opnorm R12 := by
    calc
      opnorm (R1 * E2 + E1 * R2 + R1 * R2 + T - R12)
          ≤ opnorm (R1 * E2 + E1 * R2 + R1 * R2) + opnorm (T - R12) := by
            simpa [sub_eq_add_neg, add_assoc] using h_subadd (R1 * E2 + E1 * R2 + R1 * R2) (T - R12)
      _ ≤ (opnorm (R1 * E2) + opnorm (E1 * R2) + opnorm (R1 * R2)) + (opnorm T + opnorm R12) :=
            add_le_add hsub3 hsubT
      _ = opnorm (R1 * E2) + opnorm (E1 * R2) + opnorm (R1 * R2) + opnorm T + opnorm R12 := by abel
  calc
    opnorm (R1 * E2 + E1 * R2 + R1 * R2 + T - R12)
        ≤ opnorm (R1 * E2) + opnorm (E1 * R2) + opnorm (R1 * R2) + opnorm T + opnorm R12 := hsum
    _ ≤ (5 / 2 * B * γ ^ 3) + (5 / 2 * B * γ ^ 3) + (B ^ 2 * γ ^ 3) + (5 / 4 * γ ^ 3) + (8 * B * γ
      ^ 3) := by
          exact add_le_add (add_le_add (add_le_add (add_le_add hR1E2 hE1R2) hR1R2) hT) hR12b
    _ = (13 * B + B ^ 2 + 5 / 4) * γ ^ 3 := by ring

end Matrix.ExponentialProduct.CommutatorRemainder
