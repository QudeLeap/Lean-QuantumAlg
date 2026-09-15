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
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Repeated first-order product estimates

A cubic local defect bound and a supplied unitary-product telescoping inequality
imply a repeated first-order product error estimate and a sufficient step-count
threshold for a requested precision. The exponential group law, norm-like
functional inequalities, and local bounds are hypotheses of this mathematical
result. No circuit construction or executed resource count is defined here.
-/

@[expose] public section

namespace Matrix.ExponentialProduct.Repeated

open scoped BigOperators

noncomputable section

/-- Definition: first-order Trotter factor firstOrderStep(tau) = e^{-iA tau} e^{-iB tau}. -/
def firstOrderStep {d : ℕ} (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (A B : Matrix (Fin d) (Fin d) ℂ) (τ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  expm ((-Complex.I * (τ : ℂ)) • A) * expm ((-Complex.I * (τ : ℂ)) • B)

/-- `opnorm (-X) <= opnorm X` follows from scalar sub-homogeneity with a = -1. -/
private lemma opnorm_neg_le {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (h_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (X : Matrix (Fin d) (Fin d) ℂ) : opnorm (-X) ≤ opnorm X := by
  have h := h_scalar (-1 : ℂ) X
  simpa using h

/-- `opnorm [A,B] <= 2 nu^2` for `nu = max (opnorm A) (opnorm B)`. -/
lemma comm_norm_le {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (A B : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ)
    (h_nonneg : ∀ X, 0 ≤ opnorm X)
    (h_subadd : ∀ X Y, opnorm (X + Y) ≤ opnorm X + opnorm Y)
    (h_submul : ∀ X Y, opnorm (X * Y) ≤ opnorm X * opnorm Y)
    (h_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (hν : ν = max (opnorm A) (opnorm B)) :
    opnorm (A * B - B * A) ≤ 2 * ν ^ 2 := by
  have hAν : opnorm A ≤ ν := by
    rw [hν]
    exact le_max_left _ _
  have hBν : opnorm B ≤ ν := by
    rw [hν]
    exact le_max_right _ _
  have hAB : opnorm (A * B) ≤ ν * ν := by
    exact le_trans (h_submul A B) (mul_le_mul hAν hBν (h_nonneg B) (le_trans (h_nonneg A) hAν))
  have hBA : opnorm (B * A) ≤ ν * ν := by
    exact le_trans (h_submul B A) (mul_le_mul hBν hAν (h_nonneg A) (le_trans (h_nonneg B) hBν))
  have hneg : opnorm (-(B * A)) ≤ opnorm (B * A) := opnorm_neg_le opnorm h_scalar (B * A)
  have hdec : A * B - B * A = A * B + -(B * A) := by
    rw [sub_eq_add_neg]
  calc
    opnorm (A * B - B * A) = opnorm (A * B + -(B * A)) := by rw [hdec]
    _ ≤ opnorm (A * B) + opnorm (-(B * A)) := h_subadd (A * B) (-(B * A))
    _ ≤ opnorm (A * B) + opnorm (B * A) := by
          exact add_le_add_right hneg (opnorm (A * B))
    _ ≤ ν * ν + ν * ν := add_le_add hAB hBA
    _ = 2 * ν ^ 2 := by ring

/-- Same-axis additivity iterated: `expm (-i tau X)^r = expm (-i (r*tau) X)`. -/
private lemma expm_pow {d : ℕ} (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) (r : ℕ) (τ : ℝ)
    (he0 : expm 0 = 1)
    (h_add : ∀ (X : Matrix (Fin d) (Fin d) ℂ) (τ₁ τ₂ : ℝ),
      expm ((-Complex.I * (τ₁ : ℂ)) • X) * expm ((-Complex.I * (τ₂ : ℂ)) • X) =
        expm ((-Complex.I * ((τ₁ + τ₂ : ℝ) : ℂ)) • X)) :
    expm ((-Complex.I * (τ : ℂ)) • X) ^ r =
      expm ((-Complex.I * (((r : ℝ) * τ : ℝ) : ℂ)) • X) := by
  induction r with
  | zero => simp [he0]
  | succ r ih =>
      rw [pow_succ]
      rw [ih]
      rw [h_add X ((r : ℝ) * τ) τ]
      have hre : ((r : ℝ) * τ + τ : ℝ) = ((r + 1 : ℕ) : ℝ) * τ := by
        rw [Nat.cast_add]
        ring
      rw [hre]

/-- Local third-order step bound: `opnorm (firstOrderStep - V) <= C nu^3 |tau|^3 + nu^2 tau^2`. -/
private lemma local_diff_le {d : ℕ} (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (A B : Matrix (Fin d) (Fin d) ℂ) (C ν τ : ℝ)
    (h_nonneg : ∀ X, 0 ≤ opnorm X)
    (h_subadd : ∀ X Y, opnorm (X + Y) ≤ opnorm X + opnorm Y)
    (h_submul : ∀ X Y, opnorm (X * Y) ≤ opnorm X * opnorm Y)
    (h_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (hν : ν = max (opnorm A) (opnorm B))
    (h_local : opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) +
        (((τ ^ 2 : ℝ) / 2 : ℂ) • (A * B - B * A))) ≤ C * ν ^ 3 * |τ| ^ 3) :
    opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B))) ≤
      C * ν ^ 3 * |τ| ^ 3 + ν ^ 2 * τ ^ 2 := by
  let Z : Matrix (Fin d) (Fin d) ℂ := ((τ ^ 2 : ℝ) / 2 : ℂ) • (A * B - B * A)
  have hZ : opnorm Z ≤ (τ ^ 2 / 2) * (2 * ν ^ 2) := by
    calc
      opnorm Z = opnorm (((τ ^ 2 : ℝ) / 2 : ℂ) • (A * B - B * A)) := rfl
      _ ≤ ‖((τ ^ 2 : ℝ) / 2 : ℂ)‖ * opnorm ((A * B - B * A)) :=
            h_scalar ((τ ^ 2 : ℝ) / 2) ((A * B - B * A))
      _ = (τ ^ 2 / 2) * opnorm ((A * B - B * A)) := by
            rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg (sq_nonneg τ)]
            norm_num
      _ ≤ (τ ^ 2 / 2) * (2 * ν ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (comm_norm_le opnorm A B ν h_nonneg h_subadd h_submul h_scalar hν)
              (by positivity)
  have hneg : opnorm ((-1 : ℂ) • Z) ≤ opnorm Z := by
    simpa using opnorm_neg_le opnorm h_scalar Z
  calc
    opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)))
        = opnorm ((firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) + Z) + (-1
          : ℂ) • Z) :=
          by
            congr 1
            rw [show (-1 : ℂ) • Z = -Z by simp]
            abel
    _ ≤ opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) + Z) + opnorm
      ((-1 : ℂ) •
      Z) :=
            h_subadd (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) + Z)
              ((-1 : ℂ) • Z)
    _ ≤ C * ν ^ 3 * |τ| ^ 3 + opnorm Z := add_le_add h_local hneg
    _ ≤ C * ν ^ 3 * |τ| ^ 3 + ν ^ 2 * τ ^ 2 := by
          have hZ' : opnorm Z ≤ ν ^ 2 * τ ^ 2 := by
            calc
              opnorm Z ≤ (τ ^ 2 / 2) * (2 * ν ^ 2) := hZ
              _ = ν ^ 2 * τ ^ 2 := by ring
          exact add_le_add_right hZ' (C * ν ^ 3 * |τ| ^ 3)

/-- One step of the global error bound: telescoping over r identical factors. -/
private lemma step_error_bound {d : ℕ} (r : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ)
    (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (C ν τ : ℝ) (c : ℝ)
    (h_nonneg : ∀ X, 0 ≤ opnorm X)
    (h_subadd : ∀ X Y, opnorm (X + Y) ≤ opnorm X + opnorm Y)
    (h_submul : ∀ X Y, opnorm (X * Y) ≤ opnorm X * opnorm Y)
    (h_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (he0 : expm 0 = 1)
    (h_expm_unitary : ∀ (X : Matrix (Fin d) (Fin d) ℂ) (τ : ℝ),
      IsSelfAdjoint X → expm ((-Complex.I * (τ : ℂ)) • X) ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h_expm_add : ∀ (X : Matrix (Fin d) (Fin d) ℂ) (τ₁ τ₂ : ℝ),
      expm ((-Complex.I * (τ₁ : ℂ)) • X) * expm ((-Complex.I * (τ₂ : ℂ)) • X) =
        expm ((-Complex.I * ((τ₁ + τ₂ : ℝ) : ℂ)) • X))
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hν : ν = max (opnorm A) (opnorm B))
    (hstep : ν * |τ| ≤ c)
    (h_local : ∀ τ : ℝ, ν * |τ| ≤ c →
      opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) +
        (((τ ^ 2 : ℝ) / 2 : ℂ) • (A * B - B * A))) ≤ C * ν ^ 3 * |τ| ^ 3)
    (h_telescoping : ∀ (r : ℕ) (U V : ℕ → Matrix (Fin d) (Fin d) ℂ),
      (∀ j ∈ Finset.Icc 1 r, U j ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ V j ∈ Matrix.unitaryGroup (Fin
        d) ℂ) →
        opnorm (((List.range r).map (fun i => U (i + 1))).prod -
          ((List.range r).map (fun i => V (i + 1))).prod) ≤
        Finset.sum (Finset.Icc 1 r) (fun j => opnorm (U j - V j))) :
    opnorm (((List.range r).map (fun _ => firstOrderStep expm A B τ)).prod -
      expm ((-Complex.I * (((r : ℝ) * τ : ℝ) : ℂ)) • (A + B))) ≤
      (r : ℝ) * (C * ν ^ 3 * |τ| ^ 3 + ν ^ 2 * τ ^ 2) := by
  let U : ℕ → Matrix (Fin d) (Fin d) ℂ := fun _ => firstOrderStep expm A B τ
  let V : ℕ → Matrix (Fin d) (Fin d) ℂ := fun _ => expm ((-Complex.I * (τ : ℂ)) • (A + B))
  have hAplusB : IsSelfAdjoint (A + B) := IsSelfAdjoint.add hA hB
  have hunit : ∀ j ∈ Finset.Icc 1 r,
      U j ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ V j ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    intro j hj
    constructor
    · dsimp [U, firstOrderStep]
      exact mul_mem (h_expm_unitary A τ hA) (h_expm_unitary B τ hB)
    · dsimp [V]
      exact h_expm_unitary (A + B) τ hAplusB
  have htel := h_telescoping r U V hunit
  have hprodU : ((List.range r).map (fun i => U (i + 1))).prod =
      ((List.range r).map (fun _ => firstOrderStep expm A B τ)).prod := by
    simp [U]
  have hprodV : ((List.range r).map (fun i => V (i + 1))).prod =
      expm ((-Complex.I * (τ : ℂ)) • (A + B)) ^ r := by
    simp [V, List.prod_replicate]
  have hpow : expm ((-Complex.I * (τ : ℂ)) • (A + B)) ^ r =
      expm ((-Complex.I * (((r : ℝ) * τ : ℝ) : ℂ)) • (A + B)) :=
    expm_pow expm (A + B) r τ he0 h_expm_add
  have hsum : Finset.sum (Finset.Icc 1 r) (fun j => opnorm (U j - V j)) =
      (r : ℝ) * opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B))) := by
    calc
      Finset.sum (Finset.Icc 1 r) (fun j => opnorm (U j - V j))
          = Finset.sum (Finset.Icc 1 r)
              (fun _ => opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A +
                B)))) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [U, V]
      _ = (Finset.Icc 1 r).card • opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ))
        • (A + B)))
        :=
              Finset.sum_const _
      _ = (r : ℝ) * opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)))
        := by
              rw [nsmul_eq_mul]
              congr 1
              simp
  have hdiff := local_diff_le opnorm expm A B C ν τ h_nonneg h_subadd h_submul h_scalar hν
    (h_local τ hstep)
  calc
    opnorm (((List.range r).map (fun _ => firstOrderStep expm A B τ)).prod -
        expm ((-Complex.I * (((r : ℝ) * τ : ℝ) : ℂ)) • (A + B)))
        = opnorm (((List.range r).map (fun i => U (i + 1))).prod -
            ((List.range r).map (fun i => V (i + 1))).prod) := by
            rw [hprodU, ← hpow, hprodV]
    _ ≤ Finset.sum (Finset.Icc 1 r) (fun j => opnorm (U j - V j)) := htel
    _ = (r : ℝ) * opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B))) :=
      hsum
    _ ≤ (r : ℝ) * (C * ν ^ 3 * |τ| ^ 3 + ν ^ 2 * τ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hdiff (by exact_mod_cast (Nat.zero_le r))

/-- Global algebra: `r (C nu^3 |t/r|^3 + nu^2 (t/r)^2) <= (C c + 1) nu^2 t^2 / r`
under the small-step condition `nu * (t/r) <= c`. -/
private lemma global_algebra (r : ℕ) (C ν t : ℝ) (c : ℝ)
    (hC : 0 ≤ C) (ht : 0 < t) (hr : 0 < r)
    (hstep : ν * (t / (r : ℝ)) ≤ c) :
    (r : ℝ) * (C * ν ^ 3 * |t / (r : ℝ)| ^ 3 + ν ^ 2 * (t / (r : ℝ)) ^ 2) ≤
      (C * c + 1) * (ν ^ 2 * t ^ 2 / (r : ℝ)) := by
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hτpos : 0 < t / (r : ℝ) := by positivity
  have hτabs : |t / (r : ℝ)| = t / (r : ℝ) := abs_of_pos hτpos
  have hnonneg1 : 0 ≤ C * (ν ^ 2 * t ^ 2 / (r : ℝ)) := by positivity
  calc
    (r : ℝ) * (C * ν ^ 3 * |t / (r : ℝ)| ^ 3 + ν ^ 2 * (t / (r : ℝ)) ^ 2)
        ≤ (r : ℝ) * (C * ν ^ 3 * (t / (r : ℝ)) ^ 3 + ν ^ 2 * (t / (r : ℝ)) ^ 2) := by
            rw [hτabs]
    _ = ν ^ 2 * t ^ 2 / (r : ℝ) + C * (ν ^ 2 * t ^ 2 / (r : ℝ)) * (ν * (t / (r : ℝ))) := by
            field_simp [hr_ne]
            ring
    _ ≤ ν ^ 2 * t ^ 2 / (r : ℝ) + C * (ν ^ 2 * t ^ 2 / (r : ℝ)) * c := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left hstep hnonneg1) (ν ^ 2 * t ^ 2 / (r : ℝ))
    _ = (C * c + 1) * (ν ^ 2 * t ^ 2 / (r : ℝ)) := by ring

/-- Repeated-product error and a sufficient number of steps for prescribed precision. -/
theorem error_and_precision_bound
    {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (opnorm : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (expm : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (ν c C t ε : ℝ)
    (m : ℕ)
    (h_opnorm_nonneg : ∀ X, 0 ≤ opnorm X)
    (h_opnorm_subadd : ∀ X Y, opnorm (X + Y) ≤ opnorm X + opnorm Y)
    (h_opnorm_submul : ∀ X Y, opnorm (X * Y) ≤ opnorm X * opnorm Y)
    (h_opnorm_scalar : ∀ (a : ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
      opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (h_expm_zero : expm 0 = 1)
    (h_expm_unitary : ∀ (X : Matrix (Fin d) (Fin d) ℂ) (τ : ℝ),
      IsSelfAdjoint X → expm ((-Complex.I * (τ : ℂ)) • X) ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h_expm_add : ∀ (X : Matrix (Fin d) (Fin d) ℂ) (τ₁ τ₂ : ℝ),
      expm ((-Complex.I * (τ₁ : ℂ)) • X) * expm ((-Complex.I * (τ₂ : ℂ)) • X) =
        expm ((-Complex.I * ((τ₁ + τ₂ : ℝ) : ℂ)) • X))
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hν : ν = max (opnorm A) (opnorm B))
    (h_nu_pos : 0 < ν)
    (hc_pos : 0 < c)
    (hC_pos : 0 < C)
    (ht_pos : 0 < t)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (h_m_pos : 0 < m)
    (h_local : ∀ τ : ℝ, ν * |τ| ≤ c →
      opnorm (firstOrderStep expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) +
        (((τ ^ 2 : ℝ) / 2 : ℂ) • (A * B - B * A))) ≤ C * ν ^ 3 * |τ| ^ 3)
    (h_telescoping : ∀ (r : ℕ) (U V : ℕ → Matrix (Fin d) (Fin d) ℂ),
      (∀ j ∈ Finset.Icc 1 r, U j ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ V j ∈ Matrix.unitaryGroup (Fin
        d) ℂ) →
        opnorm (((List.range r).map (fun i => U (i + 1))).prod -
          ((List.range r).map (fun i => V (i + 1))).prod) ≤
        Finset.sum (Finset.Icc 1 r) (fun j => opnorm (U j - V j)))
    (h_step_small : ν * t / (m : ℝ) ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧
      opnorm (((List.range m).map (fun _ => firstOrderStep expm A B (t / (m : ℝ)))).prod -
        expm ((-Complex.I * (t : ℂ)) • (A + B))) ≤ K * (ν ^ 2 * t ^ 2 / (m : ℝ)) ∧
      ∃ Kstep : ℝ, 0 ≤ Kstep ∧
        ∀ m' : ℕ, Kstep * (ν ^ 2 * t ^ 2 / ε) ≤ (m' : ℝ) →
          opnorm (((List.range m').map (fun _ => firstOrderStep expm A B (t / (m' : ℝ)))).prod -
            expm ((-Complex.I * (t : ℂ)) • (A + B))) ≤ ε := by
  have hε_pos : 0 < ε := hε.1
  let τ : ℝ := t / (m : ℝ)
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h_m_pos)
  have hτ_pos : 0 < τ := by dsimp [τ]; positivity
  have hτ_abs : |τ| = τ := abs_of_pos hτ_pos
  have hstep : ν * |τ| ≤ c := by
    rw [hτ_abs]
    have hconv : ν * (t / (m : ℝ)) = ν * t / (m : ℝ) := by ring
    rwa [hconv]
  have hstep2 : ν * (t / (m : ℝ)) ≤ c := by
    have hconv : ν * (t / (m : ℝ)) = ν * t / (m : ℝ) := by ring
    rwa [hconv]
  have hbound := step_error_bound m A B opnorm expm C ν τ c
    h_opnorm_nonneg h_opnorm_subadd h_opnorm_submul h_opnorm_scalar
    h_expm_zero h_expm_unitary h_expm_add hA hB hν hstep h_local h_telescoping
  have hmul : (m : ℝ) * (t / (m : ℝ)) = t := by
    field_simp [hm_ne]
  have hmain1 : opnorm (((List.range m).map (fun _ => firstOrderStep expm A B (t / (m : ℝ)))).prod -
      expm ((-Complex.I * (t : ℂ)) • (A + B))) ≤ (C * c + 1) * (ν ^ 2 * t ^ 2 / (m : ℝ)) := by
    calc
      opnorm (((List.range m).map (fun _ => firstOrderStep expm A B (t / (m : ℝ)))).prod -
          expm ((-Complex.I * (t : ℂ)) • (A + B)))
          = opnorm (((List.range m).map (fun _ => firstOrderStep expm A B τ)).prod -
              expm ((-Complex.I * (((m : ℝ) * τ : ℝ) : ℂ)) • (A + B))) := by
              congr 1
              congr 1
              rw [show (m : ℝ) * τ = t by dsimp [τ]; field_simp [hm_ne]]
      _ ≤ (m : ℝ) * (C * ν ^ 3 * |τ| ^ 3 + ν ^ 2 * τ ^ 2) := hbound
      _ ≤ (m : ℝ) * (C * ν ^ 3 * |t / (m : ℝ)| ^ 3 + ν ^ 2 * (t / (m : ℝ)) ^ 2) := by
            rfl
      _ ≤ (C * c + 1) * (ν ^ 2 * t ^ 2 / (m : ℝ)) :=
            global_algebra m C ν t c hC_pos.le ht_pos h_m_pos hstep2
  refine ⟨C * c + 1, ?_, ?_, ?_⟩
  · positivity
  · exact hmain1
  · let Kstep : ℝ := max (C * c + 1) (ε / (c * ν * t))
    refine ⟨Kstep, ?_, ?_⟩
    · dsimp [Kstep]
      exact le_max_of_le_left (by positivity)
    · intro m' hm'
      have hKstep0 : 0 < Kstep := by
        dsimp [Kstep]
        exact lt_max_of_lt_left (by positivity)
      have hscale0 : 0 < ν ^ 2 * t ^ 2 / ε := by positivity
      have hm'pos : 0 < (m' : ℝ) := lt_of_lt_of_le (mul_pos hKstep0 hscale0) hm'
      have hm'_nat : 0 < m' := by exact_mod_cast hm'pos
      have hm'ne : (m' : ℝ) ≠ 0 := ne_of_gt hm'pos
      have hτ'_abs : |t / (m' : ℝ)| = t / (m' : ℝ) := abs_of_pos (by positivity)
      have hstep' : ν * |t / (m' : ℝ)| ≤ c := by
        rw [hτ'_abs]
        have hconv : ν * (t / (m' : ℝ)) = ν * t / (m' : ℝ) := by ring
        rw [hconv]
        have hle : ν * t / c ≤ (m' : ℝ) := by
          calc
            ν * t / c = (ε / (c * ν * t)) * (ν ^ 2 * t ^ 2 / ε) := by
                field_simp [ne_of_gt hc_pos, ne_of_gt h_nu_pos, ne_of_gt ht_pos, ne_of_gt hε_pos]
            _ ≤ Kstep * (ν ^ 2 * t ^ 2 / ε) := by
                exact mul_le_mul_of_nonneg_right (le_max_right (C * c + 1) (ε / (c * ν * t)))
                  hscale0.le
            _ ≤ (m' : ℝ) := hm'
        rw [div_le_iff₀ hc_pos] at hle
        have hle2 : ν * t ≤ c * (m' : ℝ) := by simpa [mul_comm] using hle
        exact (div_le_iff₀ hm'pos).mpr hle2
      have hstep2' : ν * (t / (m' : ℝ)) ≤ c := by
        have hconv : ν * (t / (m' : ℝ)) = ν * t / (m' : ℝ) := by ring
        rw [hconv]
        rw [hτ'_abs] at hstep'
        rwa [← hconv]
      have hbound' := step_error_bound m' A B opnorm expm C ν (t / (m' : ℝ)) c
        h_opnorm_nonneg h_opnorm_subadd h_opnorm_submul h_opnorm_scalar
        h_expm_zero h_expm_unitary h_expm_add hA hB hν hstep' h_local h_telescoping
      have hmul' : (m' : ℝ) * (t / (m' : ℝ)) = t := by
        field_simp [hm'ne]
      have hmain' : opnorm (((List.range m').map (fun _ => firstOrderStep expm A B (t / (m' :
        ℝ)))).prod -
          expm ((-Complex.I * (t : ℂ)) • (A + B))) ≤ (C * c + 1) * (ν ^ 2 * t ^ 2 / (m' : ℝ)) := by
        calc
          opnorm (((List.range m').map (fun _ => firstOrderStep expm A B (t / (m' : ℝ)))).prod -
              expm ((-Complex.I * (t : ℂ)) • (A + B)))
              = opnorm (((List.range m').map (fun _ => firstOrderStep expm A B (t / (m' :
                ℝ)))).prod -
                  expm ((-Complex.I * (((m' : ℝ) * (t / (m' : ℝ)) : ℝ) : ℂ)) • (A + B))) := by
                  congr 1
                  congr 1
                  rw [show (m' : ℝ) * (t / (m' : ℝ)) = t by field_simp [hm'ne]]
          _ ≤ (m' : ℝ) * (C * ν ^ 3 * |t / (m' : ℝ)| ^ 3 + ν ^ 2 * (t / (m' : ℝ)) ^ 2) := hbound'
          _ ≤ (C * c + 1) * (ν ^ 2 * t ^ 2 / (m' : ℝ)) :=
                global_algebra m' C ν t c hC_pos.le ht_pos hm'_nat hstep2'
      have hle2 : (C * c + 1) * (ν ^ 2 * t ^ 2 / ε) ≤ (m' : ℝ) := by
        exact le_trans
          (mul_le_mul_of_nonneg_right (le_max_left (C * c + 1) (ε / (c * ν * t))) hscale0.le) hm'
      have hfinal : (C * c + 1) * (ν ^ 2 * t ^ 2 / (m' : ℝ)) ≤ ε := by
        have hle3 : (C * c + 1) * (ν ^ 2 * t ^ 2) ≤ ε * (m' : ℝ) := by
          have hmul' := mul_le_mul_of_nonneg_right hle2 hε_pos.le
          have hcancel : ((C * c + 1) * (ν ^ 2 * t ^ 2 / ε)) * ε = (C * c + 1) * (ν ^ 2 * t ^ 2)
            := by
            field_simp [ne_of_gt hε_pos]
          rw [hcancel] at hmul'
          simpa [mul_comm] using hmul'
        calc
          (C * c + 1) * (ν ^ 2 * t ^ 2 / (m' : ℝ)) = (C * c + 1) * ν ^ 2 * t ^ 2 / (m' : ℝ) := by
            ring
          _ ≤ ε := (div_le_iff₀ hm'pos).mpr (by simpa [mul_assoc, mul_left_comm, mul_comm] using
            hle3)
      exact le_trans hmain' hfinal

end

end Matrix.ExponentialProduct.Repeated
