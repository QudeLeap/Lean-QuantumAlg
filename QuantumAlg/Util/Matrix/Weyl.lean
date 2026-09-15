/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Finite Weyl matrices and transpose decomposition

Clock/shift algebra for finite complex matrices, including the transpose expansion
[CML+24, main.tex:708]. No quantum execution model is involved.
-/

@[expose] public section

namespace QuantumAlg.MatrixWeyl

noncomputable section


variable {d : ℕ}

/-! ## Clock & shift (generalized Pauli) operators -/

/-- The primitive `d`-th root of unity `ω = exp(2πi/d)` used by the clock matrix. -/
def clockRoot (d : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ))

/-- Generalized Pauli clock matrix `C = diag(1, ω, ω², …, ω^(d−1))`. -/
private def clockMatrixFormula (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j => (clockRoot d) ^ (j.val : ℕ)

/-- Generalized Pauli shift matrix `S` advancing the basis index by one modulo `d`. -/
private def shiftMatrixFormula (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if (j.val + 1) % d = i.val then 1 else 0

/-! ## Unitarity and root-of-unity identities -/

/-- `ω_d * ω̅_d = 1` (from the complex exponential identity). -/
theorem clockRoot_mul_star : clockRoot d * (starRingEnd ℂ) (clockRoot d) = 1 := by
  unfold clockRoot
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have hz0 : (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) +
      starRingEnd ℂ (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) = 0 := by
    apply Complex.ext
    · simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    · simp [Complex.div_im, Complex.mul_re, Complex.mul_im]
      ring
  rw [hz0, Complex.exp_zero]

-- Declaration-scoped exception: entrywise simp leaves the diagonal case for by_cases.
set_option linter.flexible false in
private theorem clockMatrix_mem_unitaryGroup :
    clockMatrixFormula d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  simp [clockMatrixFormula, Matrix.mul_apply, Matrix.diagonal,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have h : clockRoot d ^ (i.val : ℕ) * ((starRingEnd ℂ) (clockRoot d)) ^ (i.val : ℕ) = 1 := by
      calc
        clockRoot d ^ (i.val : ℕ) * ((starRingEnd ℂ) (clockRoot d)) ^ (i.val : ℕ)
        = (clockRoot d * (starRingEnd ℂ) (clockRoot d)) ^ (i.val : ℕ) := by ring
        _ = 1 ^ (i.val : ℕ) := by rw [clockRoot_mul_star]
        _ = 1 := by simp
    simpa using h
  · simp [hij, Ne.symm hij]

-- Declaration-scoped exception: simp exposes the finite-index equality discharged by h.
set_option linter.flexible false in
/-- `(finCycle 1)⁻¹ i = j` iff `j` is the successor of `i` modulo `d`. -/
lemma finCycle_one_symm_apply_eq_iff {d : ℕ} [NeZero d] {i j : Fin d} :
    (finCycle (1 : Fin d))⁻¹ i = j ↔ i.val = (j.val + 1) % d := by
  constructor
  · intro h
    change (finCycle (1 : Fin d)).symm i = j at h
    rw [Equiv.symm_apply_eq] at h
    rw [h]
    simp [finCycle, Fin.val_add]
  · intro h
    change (finCycle (1 : Fin d)).symm i = j
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp [finCycle, Fin.val_add]
    exact h

private theorem shiftMatrix_mem_unitaryGroup :
    shiftMatrixFormula d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  by_cases hd0 : d = 0
  · subst hd0
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    rcases i with ⟨v, hv⟩
    omega
  · have : NeZero d := ⟨hd0⟩
    have hperm : (finCycle (1 : Fin d))⁻¹.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_permMatrix]
      rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
    have hshift : shiftMatrixFormula d = (finCycle (1 : Fin d))⁻¹.permMatrix ℂ := by
      ext i j
      change (if (j.val + 1) % d = i.val then (1 : ℂ) else 0) =
        ((finCycle (1 : Fin d))⁻¹.permMatrix ℂ) i j
      simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
        Option.some.injEq]
      simp only [finCycle_one_symm_apply_eq_iff]
      by_cases h : i.val = (j.val + 1) % d
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    simpa [hshift] using hperm

/-- The finite clock operator, carrying its unitary invariant. -/
def clockMatrix (d : ℕ) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨Matrix.diagonal (fun j => clockRoot d ^ j.val), by exact clockMatrix_mem_unitaryGroup⟩

/-- Coordinate formula for the certified finite clock operator. -/
theorem clockMatrix_coe (d : ℕ) :
    (clockMatrix d : Matrix (Fin d) (Fin d) ℂ) =
      Matrix.diagonal (fun j => clockRoot d ^ j.val) := rfl

/-- The finite cyclic shift, carrying its unitary invariant. -/
def shiftMatrix (d : ℕ) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨Matrix.of (fun i j => if (j.val + 1) % d = i.val then 1 else 0), by
    exact shiftMatrix_mem_unitaryGroup⟩

/-- Coordinate formula for the certified finite cyclic shift. -/
theorem shiftMatrix_coe (d : ℕ) :
    (shiftMatrix d : Matrix (Fin d) (Fin d) ℂ) =
      Matrix.of (fun i j => if (j.val + 1) % d = i.val then 1 else 0) := rfl



local notation "Z[" d "]" => (clockMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "X[" d "]" => (shiftMatrix d : Matrix (Fin d) (Fin d) ℂ)

/-- `ω_d ^ d = 1`, the root-of-unity equation. -/
lemma clockRoot_pow_d (hd : d ≠ 0) : clockRoot d ^ d = 1 := by
  unfold clockRoot
  rw [← Complex.exp_nat_mul]
  have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have harg : (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I := by
    field_simp [hc]
  rw [harg, Complex.exp_two_pi_mul_I]

/-- `ω_d` depends on its exponent only modulo `d`. -/
lemma clockRoot_pow_mod_add (hd : d ≠ 0) (a : ℕ) :
    clockRoot d ^ (a % d) = clockRoot d ^ a := by
  rw [← Nat.div_add_mod a d, pow_add, pow_mul, clockRoot_pow_d hd, one_pow, one_mul]
  congr 1
  simp

/-- `ω_d` is a primitive `d`-th root of unity: no power below `d` is `1`. -/
lemma clockRoot_ne_one_of_pos_lt (hd : d ≠ 0) {r : ℕ} (h0 : 0 < r) (hr : r < d) :
    clockRoot d ^ r ≠ 1 := by
  intro h
  unfold clockRoot at h
  rw [← Complex.exp_nat_mul] at h
  have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hz_mul : (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (d : ℂ) := by
    calc
      (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = ((r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ))) * (d : ℂ) := by
            field_simp [hc]
      _ = ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (d : ℂ) := by rw [hn]
  have h2pi : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hrd : (r : ℂ) = (n : ℂ) * (d : ℂ) := by
    apply mul_right_cancel₀ h2pi
    simpa [mul_assoc, mul_comm, mul_left_comm] using hz_mul
  have hre : (r : ℝ) = (n : ℝ) * (d : ℝ) := by
    have h' := congrArg Complex.re hrd
    simpa using h'
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have h0r : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h0
  have hrdr : (r : ℝ) < (d : ℝ) := by exact_mod_cast hr
  have hpos : 0 < (n : ℝ) := by nlinarith
  have hlt : (n : ℝ) < 1 := by nlinarith
  have hposℤ : 0 < n := by exact_mod_cast hpos
  have hltℤ : n < 1 := by exact_mod_cast hlt
  have hn0 : n = 0 := by omega
  have hr0 : r = 0 := by
    exact_mod_cast (by simpa [hn0] using hre)
  omega

/-- The phase sum over `j : Fin d`: `Σ_j ω_d^{j*e}` is `d` when `d ∣ e` and `0` otherwise. -/
lemma sum_clockRoot_pow (hd : d ≠ 0) (e : ℕ) :
    (∑ j : Fin d, clockRoot d ^ (j.val * e)) = if e % d = 0 then (d : ℂ) else 0 := by
  by_cases he : e % d = 0
  · rw [if_pos he]
    have hpow : ∀ j : Fin d, clockRoot d ^ (j.val * e) = 1 := by
      intro j
      rw [← clockRoot_pow_mod_add hd (j.val * e)]
      have hmod : (j.val * e) % d = 0 := by
        rw [Nat.mul_mod, he, mul_zero, Nat.zero_mod]
      rw [hmod, pow_zero]
    simp [hpow]
  · rw [if_neg he]
    have hne : clockRoot d ^ e ≠ 1 := by
      have hr : e % d ≠ 0 := he
      have hmod : (e % d) < d := Nat.mod_lt e (Nat.pos_of_ne_zero hd)
      have hpos : 0 < e % d := Nat.pos_of_ne_zero hr
      have hne' : clockRoot d ^ (e % d) ≠ 1 :=
        clockRoot_ne_one_of_pos_lt hd hpos hmod
      intro h
      exact hne' (by rwa [clockRoot_pow_mod_add hd e])
    have hgeom := geom_sum_mul (clockRoot d ^ e) d
    have hsum_range : (∑ i ∈ Finset.range d, (clockRoot d ^ e) ^ i) *
        (clockRoot d ^ e - 1) = 0 := by
      rw [hgeom]
      have hpow : (clockRoot d ^ e) ^ d = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, clockRoot_pow_d hd, one_pow]
      simp [hpow]
    have hsum : (∑ j : Fin d, (clockRoot d ^ e) ^ j.val) *
        (clockRoot d ^ e - 1) = 0 := by
      rw [Fin.sum_univ_eq_sum_range]
      exact hsum_range
    have hfac : clockRoot d ^ e - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hsum' : ∑ j : Fin d, (clockRoot d ^ e) ^ j.val = 0 := by
      exact (mul_eq_zero.mp hsum).resolve_right hfac
    simpa [← pow_mul, mul_comm] using hsum'

-- Declaration-scoped exception: simp precedes the modular-successor case split.
set_option linter.flexible false in
theorem clock_shift_mul_eq_omega_smul :
    Z[d] * X[d] =
    (clockRoot d : ℂ) • (X[d] * Z[d]) := by
  by_cases hd0 : d = 0
  · subst hd0
    ext i j
    rcases i with ⟨v, hv⟩
    omega
  · ext i j
    simp [clockMatrix_coe, shiftMatrix_coe]
    by_cases hδ : (j.val + 1) % d = i.val
    · rw [if_pos hδ, if_pos hδ]
      rw [← hδ, ← pow_succ']
      exact clockRoot_pow_mod_add hd0 (j.val + 1)
    · rw [if_neg hδ, if_neg hδ]

/-- `X[d]` is the permutation matrix of `(finCycle 1)⁻¹`. -/
lemma shiftMatrix_eq_permMatrix [NeZero d] :
    X[d] = ((finCycle (1 : Fin d))⁻¹).permMatrix ℂ := by
  ext i j
  change (if (j.val + 1) % d = i.val then (1 : ℂ) else 0) =
    (((finCycle (1 : Fin d))⁻¹).permMatrix ℂ) i j
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  simp only [finCycle_one_symm_apply_eq_iff]
  by_cases h : i.val = (j.val + 1) % d
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- Powers of a permutation matrix are permutation matrices of the powers. -/
lemma permMatrix_pow (σ : Equiv.Perm (Fin d)) (k : ℕ) :
    σ.permMatrix ℂ ^ k = (σ ^ k).permMatrix ℂ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Matrix.permMatrix_mul]
      congr 1
      exact (pow_succ' σ k).symm

/-- Entrywise form of a power of the clock matrix. -/
lemma clockMatrix_pow_apply (j : ℕ) (m n : Fin d) :
    (Z[d] ^ j) m n = if m = n then clockRoot d ^ (m.val * j) else 0 := by
  rw [clockMatrix_coe, Matrix.diagonal_pow]
  simp [Matrix.diagonal_apply, pow_mul]

/-- Entrywise form of a power of the inverse clock matrix. -/
lemma clockMatrix_inv_pow_apply (j : ℕ) (m n : Fin d) :
    ((Z[d])⁻¹ ^ j) m n = if m = n then (clockRoot d ^ (m.val * j))⁻¹ else 0 := by
  have hv : IsUnit (fun i : Fin d => clockRoot d ^ i.val) := by
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero i.val (Complex.exp_ne_zero _))
  have hpt : Ring.inverse (fun i : Fin d => clockRoot d ^ i.val) =
      fun i => (clockRoot d ^ i.val)⁻¹ := by
    funext i
    rw [Ring.inverse_of_isUnit hv]
    simp
  rw [clockMatrix_coe, Matrix.inv_diagonal, Matrix.diagonal_pow]
  simp [Matrix.diagonal_apply, pow_mul, inv_pow, hpt]

/-- Entrywise form of a power of the shift matrix. -/
lemma shiftMatrix_pow_apply [NeZero d] (k : ℕ) (a b : Fin d) :
    (X[d] ^ k) a b = if ((finCycle (1 : Fin d))⁻¹ ^ k) a = b then 1 else 0 := by
  rw [shiftMatrix_eq_permMatrix, permMatrix_pow]
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]

/-- The group power of a permutation is the iterate. -/
lemma perm_pow_eq_iterate (σ : Equiv.Perm (Fin d)) (n : ℕ) (x : Fin d) :
    (σ ^ n) x = σ^[n] x := by
  revert x
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ]
      exact ih (σ x)

-- Declaration-scoped exception: simp normalizes ih before the permutation rewrites.
set_option linter.flexible false in
/-- `finCycle 1` powered `k.val` times adds `k`. -/
lemma finCycle_one_pow [NeZero d] (k : Fin d) :
    (finCycle (1 : Fin d)) ^ k.val = finCycle k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  induction k using Fin.induction with
  | zero =>
      apply Equiv.ext
      intro x
      simp [finCycle_apply]
  | succ k ih =>
      rw [Fin.val_succ, pow_succ]
      simp at ih
      rw [ih]
      apply Equiv.ext
      intro x
      rw [Equiv.Perm.mul_apply, finCycle_apply, finCycle_apply, finCycle_apply]
      apply Fin.ext
      simp [Fin.val_add]
      congr 1
      omega

/-- `(finCycle 1)^k` adds `k`: `(finCycle 1)^k b = b + k`. -/
lemma finCycle_add_apply [NeZero d] (k : Fin d) (b : Fin d) :
    ((finCycle (1 : Fin d)) ^ k.val) b = b + k := by
  rw [finCycle_one_pow]
  exact finCycle_apply k b

/-- `((finCycle 1)⁻¹)^k a = b` iff `a = b + k`. -/
lemma finCycle_pow_inv_eq_iff [NeZero d] (k : Fin d) (a b : Fin d) :
    ((finCycle (1 : Fin d))⁻¹ ^ k.val) a = b ↔ a = b + k := by
  constructor
  · intro h
    have hc : ((finCycle (1 : Fin d)) ^ k.val) (((finCycle (1 : Fin d))⁻¹ ^ k.val) a) =
        ((finCycle (1 : Fin d)) ^ k.val) b := by
      rw [h]
    have hc' : a = ((finCycle (1 : Fin d)) ^ k.val) b := by
      rw [← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel] at hc
      simpa using hc
    rw [hc', finCycle_one_pow]
    simp [finCycle_apply]
  · intro h
    have hc : (((finCycle (1 : Fin d))⁻¹ ^ k.val) a) =
        (((finCycle (1 : Fin d))⁻¹ ^ k.val) (b + k)) := by
      rw [h]
    have hb : (((finCycle (1 : Fin d))⁻¹ ^ k.val) (b + k)) = b := by
      rw [← finCycle_add_apply]
      rw [inv_pow]
      change (((finCycle (1 : Fin d)) ^ k.val).symm) (((finCycle (1 : Fin d)) ^ k.val) b) = b
      exact Equiv.symm_apply_apply _ _
    rw [hb] at hc
    exact hc

/-- Entrywise form of a power of the shift matrix: `X^k` sends `|b⟩` to `|b + k⟩`. -/
lemma shiftMatrix_pow_apply_add [NeZero d] (k : Fin d) (a b : Fin d) :
    (X[d] ^ k.val) a b = if a = b + k then 1 else 0 := by
  rw [shiftMatrix_pow_apply]
  by_cases h : ((finCycle (1 : Fin d))⁻¹ ^ k.val) a = b
  · rw [if_pos h]
    rw [if_pos ((finCycle_pow_inv_eq_iff k a b).mp h)]
  · rw [if_neg h]
    rw [if_neg (mt (finCycle_pow_inv_eq_iff k a b).mpr h)]

/-- `(ω^b)⁻¹ = ω^((d - b % d) % d)`. -/
lemma clockRoot_inv_pow (hd : d ≠ 0) (b : ℕ) :
    (clockRoot d ^ b)⁻¹ = clockRoot d ^ ((d - b % d) % d) := by
  have hr : b % d < d := Nat.mod_lt b (Nat.pos_of_ne_zero hd)
  by_cases hr0 : b % d = 0
  · have hb : clockRoot d ^ b = 1 := by
      rw [← clockRoot_pow_mod_add hd b]
      rw [hr0, pow_zero]
    rw [hb, hr0, Nat.sub_zero, Nat.mod_self, pow_zero]
    simp
  · have hpos : 0 < b % d := Nat.pos_of_ne_zero hr0
    have hsub : d - b % d < d := Nat.sub_lt (Nat.pos_of_ne_zero hd) (Nat.succ_le_of_lt hpos)
    rw [Nat.mod_eq_of_lt hsub]
    rw [← clockRoot_pow_mod_add hd b]
    have hprod : clockRoot d ^ (b % d) * clockRoot d ^ (d - b % d) = 1 := by
      rw [← pow_add]
      have hsum : b % d + (d - b % d) = d := by omega
      rw [hsum, clockRoot_pow_d hd]
    have hinv : clockRoot d ^ (d - b % d) = (clockRoot d ^ (b % d))⁻¹ := by
      refine mul_left_cancel₀ (a := clockRoot d ^ (b % d))
        (pow_ne_zero (b % d) (Complex.exp_ne_zero _)) ?_
      rw [hprod]
      exact (mul_inv_cancel₀ (pow_ne_zero (b % d) (Complex.exp_ne_zero _))).symm
    exact hinv.symm

/-- The phase identity for Lemma S2: `ω^{jm}·(ω^{j(n+k)})⁻¹ = ω^{j(m+2d-n-k)}`. -/
lemma clockRoot_phase_eq (hd : d ≠ 0) (j m n k : ℕ)
    (hn : n < d) (hk : k < d) :
    clockRoot d ^ (j * m) * (clockRoot d ^ (j * ((n + k) % d)))⁻¹ =
    clockRoot d ^ (j * ((m + 2 * d - n - k) % d)) := by
  let X := clockRoot d ^ (j * ((n + k) % d))
  have hne : X ≠ 0 := by
    dsimp [X]
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  apply mul_left_cancel₀ (a := X) hne
  have hL : X * (clockRoot d ^ (j * m) * X⁻¹) = clockRoot d ^ (j * m) := by
    calc
      X * (clockRoot d ^ (j * m) * X⁻¹)
          = X * (X⁻¹ * clockRoot d ^ (j * m)) := by
            congr 1
            rw [mul_comm]
      _ = (X * X⁻¹) * clockRoot d ^ (j * m) := by rw [← mul_assoc]
      _ = 1 * clockRoot d ^ (j * m) := by rw [mul_inv_cancel₀ hne]
      _ = clockRoot d ^ (j * m) := by rw [one_mul]
  have hR : X * clockRoot d ^ (j * ((m + 2 * d - n - k) % d)) = clockRoot d ^ (j * m) := by
    rw [← pow_add]
    have hE : clockRoot d ^ (j * ((n + k) % d) + j * ((m + 2 * d - n - k) % d)) =
        clockRoot d ^ ((j * ((n + k) % d) + j * ((m + 2 * d - n - k) % d)) % d) := by
      exact (clockRoot_pow_mod_add hd _).symm
    rw [hE]
    have hT : clockRoot d ^ (j * m) = clockRoot d ^ ((j * m) % d) := by
      exact (clockRoot_pow_mod_add hd (j * m)).symm
    rw [hT]
    congr 1
    have h1 : (j * ((n + k) % d)) % d = (j * (n + k)) % d := by
      simp [Nat.mul_mod]
    have h2 : (j * ((m + 2 * d - n - k) % d)) % d = (j * (m + 2 * d - n - k)) % d := by
      simp [Nat.mul_mod]
    rw [Nat.add_mod, h1, h2, ← Nat.add_mod]
    have hsum : j * (n + k) + j * (m + 2 * d - n - k) = j * (m + 2 * d) := by
      rw [← left_distrib]
      congr 1
      omega
    rw [hsum]
    have hmod2 : (m + 2 * d) % d = m % d := by simp
    calc
      (j * (m + 2 * d)) % d = ((j % d) * ((m + 2 * d) % d)) % d := by rw [Nat.mul_mod]
      _ = ((j % d) * (m % d)) % d := by rw [hmod2]
      _ = (j * m) % d := by rw [← Nat.mul_mod]
  rw [hL]
  rw [hR]

/-- `(a - b) + b = a` for `Fin`. -/
lemma fin_sub_add_cancel (a b : Fin d) : (a - b) + b = a := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_sub]
  by_cases hlt : a.val < b.val
  · have hb : d - b.val + a.val < d := by omega
    have hsub1 : (d - b.val + a.val) % d = d - b.val + a.val := Nat.mod_eq_of_lt hb
    rw [hsub1]
    have h1 : d - b.val + a.val + b.val = d + a.val := by omega
    rw [h1]
    rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt a.isLt]
  · have hge : b.val ≤ a.val := Nat.le_of_not_gt hlt
    have hsub1 : (d - b.val + a.val) % d = (a.val - b.val) % d := by
      have hx : d - b.val + a.val = (a.val - b.val) + d := by omega
      rw [hx]
      rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    rw [hsub1]
    have hsub2 : a.val - b.val < d := by omega
    rw [Nat.mod_eq_of_lt hsub2]
    have h1 : a.val - b.val + b.val = a.val := Nat.sub_add_cancel hge
    rw [h1]
    rw [Nat.mod_eq_of_lt a.isLt]

-- Declaration-scoped exception: simp expands products before indexed sum collapse.
set_option linter.flexible false in
/-- Entrywise collapse of the Lemma S2 summand. -/
lemma zx_uzx_entry [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) (m n : Fin d) :
    ∀ j k : Fin d,
      (Z[d] ^ j.val * X[d] ^ k.val * U *
        (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) m n =
      clockRoot d ^ (j.val * m.val) * U (m - k) (n + k) *
        (clockRoot d ^ (j.val * ((n.val + k.val) % d)))⁻¹ := by
  intro j k
  simp [Matrix.mul_apply, clockMatrix_pow_apply, clockMatrix_inv_pow_apply,
    shiftMatrix_pow_apply_add, Fin.val_add]
  rw [Finset.sum_eq_single (m - k)]
  · have hk : m = (m - k) + k := (fin_sub_add_cancel m k).symm
    rw [if_pos hk]
    have h1 : clockRoot d ^ (m.val * j.val) = clockRoot d ^ (j.val * m.val) := by
      congr 1
      rw [mul_comm]
    have h2 : (clockRoot d ^ (((n.val + k.val) % d) * j.val))⁻¹ =
        (clockRoot d ^ (j.val * ((n.val + k.val) % d)))⁻¹ := by
      congr 1
      congr 1
      rw [mul_comm]
    rw [h1, h2]
  · intro x hx hxk
    rw [if_neg]
    intro hm
    apply hxk
    apply Fin.ext
    have hmv : m.val = (x.val + k.val) % d := by
      rw [hm]
      simp [Fin.val_add]
    rw [Fin.val_sub, hmv]
    by_cases hlt : x.val + k.val < d
    · rw [Nat.mod_eq_of_lt hlt]
      have h1 : d - k.val + (x.val + k.val) = x.val + d := by omega
      rw [h1]
      rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt x.isLt]
    · have hge : d ≤ x.val + k.val := Nat.le_of_not_gt hlt
      rw [Nat.mod_eq_sub_mod hge]
      have hsub : x.val + k.val - d < d := by omega
      rw [Nat.mod_eq_of_lt hsub]
      have h2 : d - k.val + (x.val + k.val - d) = x.val := by omega
      rw [h2]
      rw [Nat.mod_eq_of_lt x.isLt]
  · intro h
    exact False.elim (h (Finset.mem_univ (m - k)))

/-- The representative of `m - n` modulo `d`. -/
lemma s2_k0_mod {m n : ℕ} (hm : m < d) (hn : n < d) :
    (m + d - n) % d = if n ≤ m then m - n else m + d - n := by
  by_cases hge : n ≤ m
  · rw [if_pos hge]
    have hx : m + d - n = (m - n) + d := by omega
    rw [hx]
    have hlt : m - n < d := by omega
    rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hlt]
  · rw [if_neg hge]
    have hlt : m + d - n < d := by omega
    rw [Nat.mod_eq_of_lt hlt]

lemma s2_k0_sub {m n : ℕ} (hm : m < d) (hn : n < d) :
    (m + d - (m + d - n) % d) % d = n := by
  by_cases hge : n ≤ m
  · have hk0 : (m + d - n) % d = m - n := by
      rw [s2_k0_mod hm hn, if_pos hge]
    rw [hk0]
    have hx : m + d - (m - n) = d + n := by
      have hm' : m = n + (m - n) := (Nat.add_sub_of_le hge).symm
      rw [hm']
      omega
    rw [hx]
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hn]
  · have hk0 : (m + d - n) % d = m + d - n := by
      rw [s2_k0_mod hm hn, if_neg hge]
    rw [hk0]
    have hx : m + d - (m + d - n) = n := by omega
    rw [hx]
    rw [Nat.mod_eq_of_lt hn]

lemma s2_k0_add {m n : ℕ} (hm : m < d) (hn : n < d) :
    (n + (m + d - n) % d) % d = m := by
  by_cases hge : n ≤ m
  · have hk0 : (m + d - n) % d = m - n := by
      rw [s2_k0_mod hm hn, if_pos hge]
    rw [hk0]
    have hx : n + (m - n) = m := Nat.add_sub_of_le hge
    rw [hx]
    rw [Nat.mod_eq_of_lt hm]
  · have hk0 : (m + d - n) % d = m + d - n := by
      rw [s2_k0_mod hm hn, if_neg hge]
    rw [hk0]
    have hx : n + (m + d - n) = m + d := by omega
    rw [hx]
    rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hm]

/-- The unique `k` with `(m + 2d - n - k) % d = 0` is `(m + d - n) % d`. -/
lemma s2_k0_eq {m n k : ℕ} (hm : m < d) (hn : n < d) (hk : k < d) :
    (m + 2 * d - n - k) % d = 0 ↔ k = (m + d - n) % d := by
  constructor
  · intro h
    have hmod : Nat.ModEq d (m + 2 * d - n - k) 0 := by
      simpa [Nat.ModEq] using h
    have hkadd : Nat.ModEq d (m + 2 * d - n - k + k) k := by
      simpa using hmod.add_right k
    have hsum : m + 2 * d - n - k + k = m + 2 * d - n := by omega
    have hk2 : Nat.ModEq d (m + 2 * d - n) k := by
      rwa [hsum] at hkadd
    have hmod2 : (m + 2 * d - n) % d = (m + d - n) % d := by
      have hx : m + 2 * d - n = (m + d - n) + d := by omega
      rw [hx]
      rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    have hk3 : k % d = (m + d - n) % d := by
      rw [Nat.ModEq, hmod2] at hk2
      exact hk2.symm
    rw [← Nat.mod_eq_of_lt hk]
    exact hk3
  · intro h
    rw [h]
    by_cases hge : n ≤ m
    · have hr : (m + d - n) % d = m - n := by
        rw [s2_k0_mod hm hn, if_pos hge]
      rw [hr]
      have hx : m + 2 * d - n - (m - n) = 2 * d := by
        have hm' : m = n + (m - n) := (Nat.add_sub_of_le hge).symm
        rw [hm']
        omega
      rw [hx]
      simp
    · have hr : (m + d - n) % d = m + d - n := by
        rw [s2_k0_mod hm hn, if_neg hge]
      rw [hr]
      have hx : m + 2 * d - n - (m + d - n) = d := by
        have h1 : m + 2 * d - n = (m + d - n) + d := by omega
        rw [h1]
        omega
      rw [hx, Nat.mod_self]

/-! ## Lemma S2: LCU decomposition of `Uᵀ` -/

lemma matrix_transpose_decompose (U : Matrix (Fin d) (Fin d) ℂ) :
    U.transpose = (1 / (d : ℂ)) • (∑ j : Fin d, ∑ k : Fin d,
      (Z[d] ^ (j.val : ℕ)) * (X[d] ^ (k.val : ℕ)) *
      U * ((Z[d])⁻¹ ^ (j.val : ℕ)) * (X[d] ^ (k.val : ℕ))) := by
  by_cases hd0 : d = 0
  · subst hd0
    ext i j
    rcases i with ⟨v, hv⟩
    omega
  · have : NeZero d := ⟨hd0⟩
    ext m n
    rw [Matrix.transpose_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    have hint := zx_uzx_entry U m n
    simp_rw [hint]
    rw [Finset.sum_comm]
    have hphase : ∀ k : Fin d,
        (∑ j : Fin d, clockRoot d ^ (j.val * m.val) * U (m - k) (n + k) *
            (clockRoot d ^ (j.val * ((n.val + k.val) % d)))⁻¹) =
        (if (m.val + 2 * d - n.val - k.val) % d = 0 then (d : ℂ) else 0) *
          U (m - k) (n + k) := by
      intro k
      have hsum : (∑ j : Fin d, clockRoot d ^ (j.val * m.val) * U (m - k) (n + k) *
            (clockRoot d ^ (j.val * ((n.val + k.val) % d)))⁻¹) =
          (∑ j : Fin d, clockRoot d ^ (j.val * ((m.val + 2 * d - n.val - k.val) % d)) *
            U (m - k) (n + k)) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          clockRoot d ^ (j.val * m.val) * U (m - k) (n + k) *
              (clockRoot d ^ (j.val * ((n.val + k.val) % d)))⁻¹
              = (clockRoot d ^ (j.val * m.val) *
                  (clockRoot d ^ (j.val * ((n.val + k.val) % d)))⁻¹) * U (m - k) (n + k) := by
                ring
          _ = clockRoot d ^ (j.val * ((m.val + 2 * d - n.val - k.val) % d)) *
                U (m - k) (n + k) := by
                rw [clockRoot_phase_eq hd0 j.val m.val n.val k.val n.isLt k.isLt]
      rw [hsum]
      rw [← Finset.sum_mul]
      rw [sum_clockRoot_pow hd0 ((m.val + 2 * d - n.val - k.val) % d)]
      simp
    simp_rw [hphase]
    let k0 : Fin d := ⟨(m.val + d - n.val) % d,
      Nat.mod_lt (m.val + d - n.val) (Nat.pos_of_ne_zero hd0)⟩
    have hsumk : (∑ k : Fin d,
        (if (m.val + 2 * d - n.val - k.val) % d = 0 then (d : ℂ) else 0) *
          U (m - k) (n + k)) = (d : ℂ) * U n m := by
      rw [Finset.sum_eq_single k0]
      · have he0 : (m.val + 2 * d - n.val - k0.val) % d = 0 :=
          (s2_k0_eq m.isLt n.isLt k0.isLt).mpr rfl
        have hsub : m - k0 = n := by
          apply Fin.ext
          rw [Fin.val_sub]
          have hx : d - k0.val + m.val = m.val + d - k0.val := by omega
          rw [hx]
          exact s2_k0_sub m.isLt n.isLt
        have hadd : n + k0 = m := by
          apply Fin.ext
          rw [Fin.val_add]
          exact s2_k0_add m.isLt n.isLt
        rw [if_pos he0, hsub, hadd]
      · intro k hk hne
        have he : (m.val + 2 * d - n.val - k.val) % d ≠ 0 := by
          intro hz
          apply hne
          apply Fin.ext
          simpa using (s2_k0_eq m.isLt n.isLt k.isLt).mp hz
        rw [if_neg he]
        ring
      · intro h
        exact False.elim (h (Finset.mem_univ k0))
    rw [hsumk]
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd0]

/-- QFT normalization factor: `1/√d`. -/
def invSqrtD (d : ℕ) : ℂ := (↑(Real.sqrt (d : ℝ)))⁻¹

theorem invSqrtD_ne_zero (hd : d ≠ 0) : invSqrtD d ≠ 0 :=
  inv_ne_zero <| Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast (Nat.pos_of_ne_zero hd))

theorem invSqrtD_mul_self (d : ℕ) :
    invSqrtD d * invSqrtD d = (↑(d : ℝ))⁻¹ := by
  rw [invSqrtD, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg d)]

@[simp]
theorem star_invSqrtD (d : ℕ) : star (invSqrtD d) = invSqrtD d := by
  rw [invSqrtD, star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem clockRoot_ne_zero (d : ℕ) : clockRoot d ≠ 0 :=
  Complex.exp_ne_zero _

/-- `clockRoot d` is a primitive `d`-th root of unity. -/
theorem clockRoot_isPrimitiveRoot (hd : d ≠ 0) :
    IsPrimitiveRoot (clockRoot d) d := by
  simpa [clockRoot] using Complex.isPrimitiveRoot_exp d hd

/-- `‖ω_d‖ = 1`. -/
theorem norm_clockRoot (hd : d ≠ 0) : ‖clockRoot d‖ = 1 := by
  have hz : 2 * (Real.pi : ℂ) * Complex.I / (d : ℂ) =
      ((2 * Real.pi / (d : ℝ) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    · simp [Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
  rw [clockRoot, hz]
  exact Complex.norm_exp_ofReal_mul_I _

@[simp]
theorem star_clockRoot (hd : d ≠ 0) : star (clockRoot d) = (clockRoot d)⁻¹ := by
  rw [Complex.star_def, ← RCLike.inv_eq_conj (norm_clockRoot hd)]

theorem clockRoot_zpow_eq_one_iff (hd : d ≠ 0) (m : ℤ) :
    clockRoot d ^ m = 1 ↔ ((d : ℕ) : ℤ) ∣ m :=
  (clockRoot_isPrimitiveRoot hd).zpow_eq_one_iff_dvd m

theorem sum_clockRoot_zpow_eq_zero (hd : d ≠ 0) {r : ℤ}
    (hr : ¬ ((d : ℕ) : ℤ) ∣ r) :
    ∑ l : Fin d, clockRoot d ^ ((l.val : ℤ) * r) = 0 := by
  have hsum : ∀ l : Fin d,
      clockRoot d ^ ((l.val : ℤ) * r) = (clockRoot d ^ r) ^ l.val := fun l => by
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp only [hsum]
  rw [Fin.sum_univ_eq_sum_range fun i => (clockRoot d ^ r) ^ i]
  have hne1 : clockRoot d ^ r ≠ 1 := fun h => hr ((clockRoot_zpow_eq_one_iff hd r).mp h)
  have hd' : (clockRoot d ^ r) ^ d = 1 := by
    rw [← zpow_natCast (clockRoot d ^ r) d, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, clockRoot_pow_d hd, one_zpow]
  rw [geom_sum_eq hne1, hd', sub_self, zero_div]

/-- `Z† = Z⁻¹` for the clock matrix. -/
lemma clockMatrix_conjTranspose [NeZero d] :
    (Z[d]).conjTranspose = (Z[d])⁻¹ := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  rw [show Z[d] b a = if b = a then clockRoot d ^ b.val else 0 by
    simp [clockMatrix_coe, Matrix.diagonal_apply]]
  rw [show (Z[d])⁻¹ = (Z[d])⁻¹ ^ (1 : ℕ) by simp]
  rw [clockMatrix_inv_pow_apply 1]
  by_cases hab : b = a
  · subst hab
    rw [if_pos rfl]
    rw [if_pos rfl]
    rw [star_pow]
    rw [star_clockRoot (NeZero.ne d)]
    rw [inv_pow]
    simp
  · rw [if_neg hab]
    rw [if_neg (by intro h; exact hab h.symm)]
    simp

/-- `X† = X⁻¹` for the shift matrix. -/
lemma shiftMatrix_conjTranspose :
    (X[d]).conjTranspose = (X[d])⁻¹ := by
  have hmem : X[d] ∈ Matrix.unitaryGroup (Fin d) ℂ := (shiftMatrix d).property
  have hmul : X[d] * (X[d]).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem
  have hmul' : (X[d]).conjTranspose * X[d] = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hmem
  let u : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
    ⟨X[d], (X[d]).conjTranspose, hmul, hmul'⟩
  rw [← Matrix.coe_units_inv u]
  rfl

/-- `(Z^k)† = Z^{-k}`. -/
lemma clockMatrix_pow_conjTranspose [NeZero d] (k : Fin d) :
    (Z[d] ^ k.val).conjTranspose = (Z[d])⁻¹ ^ k.val := by
  rw [Matrix.conjTranspose_pow]
  rw [clockMatrix_conjTranspose]

/-- `(Z^{-k})† = Z^k`. -/
lemma clockMatrix_inv_pow_conjTranspose [NeZero d] (k : Fin d) :
    ((Z[d])⁻¹ ^ k.val).conjTranspose = Z[d] ^ k.val := by
  rw [Matrix.conjTranspose_pow]
  have h : ((Z[d])⁻¹).conjTranspose = Z[d] := by
    rw [← clockMatrix_conjTranspose]
    simp
  rw [h]

/-- `(X^k)† = X^{-k}`. -/
lemma shiftMatrix_pow_conjTranspose (k : Fin d) :
    (X[d] ^ k.val).conjTranspose = (X[d])⁻¹ ^ k.val := by
  rw [Matrix.conjTranspose_pow]
  rw [shiftMatrix_conjTranspose]

/-- `(X^{-k})† = X^k`. -/
lemma shiftMatrix_inv_pow_conjTranspose (k : Fin d) :
    ((X[d])⁻¹ ^ k.val).conjTranspose = X[d] ^ k.val := by
  rw [Matrix.conjTranspose_pow]
  have h : ((X[d])⁻¹).conjTranspose = X[d] := by
    rw [← shiftMatrix_conjTranspose]
    simp
  rw [h]

/-- `Z^k · Z^{-k} = 1` and `Z^{-k} · Z^k = 1`. -/
lemma clockMatrix_pow_mul_inv_pow (k : Fin d) :
    Z[d] ^ k.val * (Z[d])⁻¹ ^ k.val = 1 := by
  -- (Z⁻¹)^k = (Z^k)⁻¹
  have h1 : (Z[d])⁻¹ ^ k.val = (Z[d] ^ k.val)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [Ring.inverse_pow]
    rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [h1]
  -- (Z^k)⁻¹ = (Z^k)† and Z^k · (Z^k)† = 1
  have hmem : Z[d] ^ k.val ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    exact pow_mem (clockMatrix d).property k.val
  have hmul : (Z[d] ^ k.val) * (Z[d] ^ k.val).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem
  have hmul' : (Z[d] ^ k.val).conjTranspose * (Z[d] ^ k.val) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hmem
  let u : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
    ⟨Z[d] ^ k.val, (Z[d] ^ k.val).conjTranspose, hmul, hmul'⟩
  have hinv : (Z[d] ^ k.val)⁻¹ = (Z[d] ^ k.val).conjTranspose := by
    rw [← Matrix.coe_units_inv u]
    rfl
  rw [hinv]
  exact hmul

/-- `X^k · X^{-k} = 1`. -/
lemma shiftMatrix_pow_mul_inv_pow (k : Fin d) :
    X[d] ^ k.val * (X[d])⁻¹ ^ k.val = 1 := by
  have h1 : (X[d])⁻¹ ^ k.val = (X[d] ^ k.val)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [Ring.inverse_pow]
    rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [h1]
  have hmem : X[d] ^ k.val ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    exact pow_mem (shiftMatrix d).property k.val
  have hmul : (X[d] ^ k.val) * (X[d] ^ k.val).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem
  have hmul' : (X[d] ^ k.val).conjTranspose * (X[d] ^ k.val) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hmem
  let u : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
    ⟨X[d] ^ k.val, (X[d] ^ k.val).conjTranspose, hmul, hmul'⟩
  have hinv : (X[d] ^ k.val)⁻¹ = (X[d] ^ k.val).conjTranspose := by
    rw [← Matrix.coe_units_inv u]
    rfl
  rw [hinv]
  exact hmul

/-- `Z^{-k} · Z^k = 1`. -/
lemma clockMatrix_inv_pow_mul_pow [NeZero d] (k : Fin d) :
    (Z[d])⁻¹ ^ k.val * Z[d] ^ k.val = 1 := by
  rw [show (Z[d])⁻¹ ^ k.val = (Z[d] ^ k.val).conjTranspose by
    exact (clockMatrix_pow_conjTranspose k).symm]
  exact Matrix.mem_unitaryGroup_iff'.mp (pow_mem (clockMatrix d).property k.val)

/-- `X^{-k} · X^k = 1`. -/
lemma shiftMatrix_inv_pow_mul_pow (k : Fin d) :
    (X[d])⁻¹ ^ k.val * X[d] ^ k.val = 1 := by
  rw [show (X[d])⁻¹ ^ k.val = (X[d] ^ k.val).conjTranspose by
    exact (shiftMatrix_pow_conjTranspose k).symm]
  exact Matrix.mem_unitaryGroup_iff'.mp (pow_mem (shiftMatrix d).property k.val)

/-- Each decoder block `M_{jk} = X^{-j} Z^{-k} U X^{-j} Z^k` is unitary. -/

lemma shiftMatrix_inv_pow_mem_unitaryGroup (j : Fin d) :
    (X[d])⁻¹ ^ j.val ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  have hmem : X[d] ^ j.val ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    pow_mem (shiftMatrix d).property j.val
  let u : Matrix.unitaryGroup (Fin d) ℂ := ⟨X[d] ^ j.val, hmem⟩
  have h1 : (X[d])⁻¹ ^ j.val = ↑u⁻¹ := by
    have hpow : (X[d])⁻¹ ^ j.val = (X[d] ^ j.val)⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
      rw [Ring.inverse_pow]
      rw [← Matrix.nonsing_inv_eq_ringInverse]
    rw [hpow]
    have hmul : (X[d] ^ j.val) * (X[d] ^ j.val).conjTranspose = 1 :=
      Matrix.mem_unitaryGroup_iff.mp hmem
    have hmul' : (X[d] ^ j.val).conjTranspose * (X[d] ^ j.val) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hmem
    let w : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
      ⟨X[d] ^ j.val, (X[d] ^ j.val).conjTranspose, hmul, hmul'⟩
    have hinv : (X[d] ^ j.val)⁻¹ = (X[d] ^ j.val).conjTranspose := by
      rw [← Matrix.coe_units_inv w]
      rfl
    rw [hinv]
    rw [← Matrix.star_eq_conjTranspose]
    rw [Matrix.UnitaryGroup.inv_val u]
  rw [h1]
  exact u⁻¹.2

/-- `Z^{-k} ∈ unitaryGroup`. -/
lemma clockMatrix_inv_pow_mem_unitaryGroup (k : Fin d) :
    (Z[d])⁻¹ ^ k.val ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  have hmem : Z[d] ^ k.val ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    pow_mem (clockMatrix d).property k.val
  let u : Matrix.unitaryGroup (Fin d) ℂ := ⟨Z[d] ^ k.val, hmem⟩
  have h1 : (Z[d])⁻¹ ^ k.val = ↑u⁻¹ := by
    have hpow : (Z[d])⁻¹ ^ k.val = (Z[d] ^ k.val)⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
      rw [Ring.inverse_pow]
      rw [← Matrix.nonsing_inv_eq_ringInverse]
    rw [hpow]
    have hmul : (Z[d] ^ k.val) * (Z[d] ^ k.val).conjTranspose = 1 :=
      Matrix.mem_unitaryGroup_iff.mp hmem
    have hmul' : (Z[d] ^ k.val).conjTranspose * (Z[d] ^ k.val) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hmem
    let w : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
      ⟨Z[d] ^ k.val, (Z[d] ^ k.val).conjTranspose, hmul, hmul'⟩
    have hinv : (Z[d] ^ k.val)⁻¹ = (Z[d] ^ k.val).conjTranspose := by
      rw [← Matrix.coe_units_inv w]
      rfl
    rw [hinv]
    rw [← Matrix.star_eq_conjTranspose]
    rw [Matrix.UnitaryGroup.inv_val u]
  rw [h1]
  exact u⁻¹.2

/-- `U.map star` is unitary when `U` is. -/
lemma map_star_mem_unitaryGroup (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    U.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose]
  have hUU : U * U.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have hct : (U.map (starRingEnd ℂ)).conjTranspose = U.transpose := by
    ext i j
    rw [Matrix.conjTranspose_apply]
    simp [Matrix.map_apply]
  rw [hct]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  have hstar : (∑ c : Fin d, starRingEnd ℂ (U a c) * U b c) = star ((U * U.conjTranspose) a b) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    rw [show star (∑ j : Fin d, U a j * star (U b j)) = ∑ j : Fin d, U b j * starRingEnd ℂ (U a j)
    by
      simp [mul_comm]]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hstar, hUU]
  simp [Matrix.one_apply]

end

end QuantumAlg.MatrixWeyl
