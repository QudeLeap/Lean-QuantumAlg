/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.Real.Trig.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified rational enclosures of dyadic angles

Taylor truncation and uncertainty in pi contribute separately to the radius.
The default twenty-decimal pi interval supports up to 56 requested bits.
Finer user-supplied pi intervals support arbitrary precision through the same
soundness and accuracy theorems.
-/

@[expose] public section

namespace QuantumAlg.TrigEnclosure

/-- Rational pi bounds certified against the real constant. -/
structure PiBounds where
  /-- Rational lower endpoint. -/
  lo : ℚ
  /-- Rational upper endpoint. -/
  hi : ℚ
  lo_nonneg : 0 ≤ lo
  lo_le_pi : (lo : ℝ) ≤ Real.pi
  pi_le_hi : Real.pi ≤ (hi : ℝ)
  hi_le_four : hi ≤ 4

/-- Mathlib's twenty-decimal rational enclosure of pi. -/
def pi20 : PiBounds where
  lo := 3.14159265358979323846
  hi := 3.14159265358979323847
  lo_nonneg := by norm_num
  lo_le_pi := by exact le_of_lt Real.pi_gt_d20
  pi_le_hi := by exact le_of_lt Real.pi_lt_d20
  hi_le_four := by norm_num

/-- Rational lower-end approximation of the angle. -/
def angleApprox (j : ℕ) (p : PiBounds := pi20) : ℚ := 2 * p.lo / 2 ^ j

/-- Certified radius: a Taylor remainder plus the angle uncertainty. -/
def radius (j n : ℕ) (p : PiBounds := pi20) : ℚ :=
  2 / (n + 4).factorial + 2 * (p.hi - p.lo) / 2 ^ j

/-- Rational lower enclosure of cosine. -/
def cosLo (j n : ℕ) (p : PiBounds := pi20) : ℚ :=
  cosPoly (angleApprox j p) (n + 4) - radius j n p

/-- Rational upper enclosure of cosine. -/
def cosHi (j n : ℕ) (p : PiBounds := pi20) : ℚ :=
  cosPoly (angleApprox j p) (n + 4) + radius j n p

/-- Rational lower enclosure of sine. -/
def sinLo (j n : ℕ) (p : PiBounds := pi20) : ℚ :=
  sinPoly (angleApprox j p) (n + 4) - radius j n p

/-- Rational upper enclosure of sine. -/
def sinHi (j n : ℕ) (p : PiBounds := pi20) : ℚ :=
  sinPoly (angleApprox j p) (n + 4) + radius j n p

private lemma lo_le_hi (p : PiBounds) : p.lo ≤ p.hi := by
  exact_mod_cast p.lo_le_pi.trans p.pi_le_hi

private lemma denominator_ge_eight (j : ℕ) (hj : 3 ≤ j) : (8 : ℝ) ≤ 2 ^ j := by
  have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hj
  norm_num at this ⊢
  exact this

private lemma angleApprox_abs_le_one (j : ℕ) (p : PiBounds) (hj : 3 ≤ j) :
    |(angleApprox j p : ℝ)| ≤ 1 := by
  have hlo : (0 : ℝ) ≤ p.lo := by exact_mod_cast p.lo_nonneg
  have hhi : (p.lo : ℝ) ≤ 4 := by exact_mod_cast (lo_le_hi p).trans p.hi_le_four
  have hd := denominator_ge_eight j hj
  simp only [angleApprox, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

private lemma angle_error (j : ℕ) (p : PiBounds) :
    |2 * Real.pi / 2 ^ j - (angleApprox j p : ℝ)| ≤
      (2 * (p.hi - p.lo) / 2 ^ j : ℚ) := by
  have hden : (0 : ℝ) < 2 ^ j := by positivity
  have hp := p.lo_le_pi
  have hp' := p.pi_le_hi
  simp only [angleApprox, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_sub]
  rw [← sub_div, ← mul_sub, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (le_of_lt hden)
  linarith

private lemma cos_center_error (j n : ℕ) (p : PiBounds) (hj : 3 ≤ j) :
    |Real.cos (2 * Real.pi / 2 ^ j) - (cosPoly (angleApprox j p) (n + 4) : ℝ)| ≤
      (radius j n p : ℝ) := by
  have h1 := (Real.abs_cos_sub_cos_le (2 * Real.pi / 2 ^ j)
    (angleApprox j p)).trans (angle_error j p)
  have h2 := cosPoly_error (angleApprox j p) (n + 4)
    (angleApprox_abs_le_one j p hj) (by omega)
  have h := (abs_sub_le (Real.cos (2 * Real.pi / 2 ^ j))
    (Real.cos (angleApprox j p)) (cosPoly (angleApprox j p) (n + 4))).trans
    (add_le_add h1 h2)
  simpa [radius, add_comm] using h

private lemma sin_center_error (j n : ℕ) (p : PiBounds) (hj : 3 ≤ j) :
    |Real.sin (2 * Real.pi / 2 ^ j) - (sinPoly (angleApprox j p) (n + 4) : ℝ)| ≤
      (radius j n p : ℝ) := by
  have h1 := (Real.abs_sin_sub_sin_le (2 * Real.pi / 2 ^ j)
    (angleApprox j p)).trans (angle_error j p)
  have h2 := sinPoly_error (angleApprox j p) (n + 4)
    (angleApprox_abs_le_one j p hj) (by omega)
  have h := (abs_sub_le (Real.sin (2 * Real.pi / 2 ^ j))
    (Real.sin (angleApprox j p)) (sinPoly (angleApprox j p) (n + 4))).trans
    (add_le_add h1 h2)
  simpa [radius, add_comm] using h

lemma cosLo_le_cos (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds := pi20) :
    (cosLo j n p : ℝ) ≤ Real.cos (2 * Real.pi / 2 ^ j) := by
  have h := (abs_le.mp (cos_center_error j n p hj)).1
  simp only [cosLo, Rat.cast_sub]
  linarith

lemma cos_le_cosHi (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds := pi20) :
    Real.cos (2 * Real.pi / 2 ^ j) ≤ (cosHi j n p : ℝ) := by
  have h := (abs_le.mp (cos_center_error j n p hj)).2
  simp only [cosHi, Rat.cast_add]
  linarith

lemma sinLo_le_sin (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds := pi20) :
    (sinLo j n p : ℝ) ≤ Real.sin (2 * Real.pi / 2 ^ j) := by
  have h := (abs_le.mp (sin_center_error j n p hj)).1
  simp only [sinLo, Rat.cast_sub]
  linarith

lemma sin_le_sinHi (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds := pi20) :
    Real.sin (2 * Real.pi / 2 ^ j) ≤ (sinHi j n p : ℝ) := by
  have h := (abs_le.mp (sin_center_error j n p hj)).2
  simp only [sinHi, Rat.cast_add]
  linarith

private lemma truncation_width_le (n : ℕ) :
    (4 : ℚ) / (n + 4).factorial ≤ 1 / 2 ^ n / 2 := by
  have hf : (2 : ℚ) ^ (n + 3) ≤ (n + 4).factorial := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := n + 3)
    norm_num [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at h
    exact_mod_cast h
  calc
    _ ≤ 4 / (2 : ℚ) ^ (n + 3) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hf
    _ = _ := by rw [pow_add]; norm_num; ring

/-- The chosen truncation meets the requested accuracy whenever pi is accurate enough. -/
lemma radius_accuracy (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds)
    (hp : p.hi - p.lo ≤ 1 / (2 : ℚ) ^ n) :
    2 * radius j n p ≤ 1 / (2 : ℚ) ^ n := by
  have hd : (8 : ℚ) ≤ 2 ^ j := by exact_mod_cast denominator_ge_eight j hj
  have hgap : 0 ≤ p.hi - p.lo := sub_nonneg.mpr (lo_le_hi p)
  have hangle : 4 * (p.hi - p.lo) / 2 ^ j ≤ (p.hi - p.lo) / 2 := by
    calc
      _ ≤ 4 * (p.hi - p.lo) / 8 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
      _ = _ := by ring
  have ht := truncation_width_le n
  calc
    _ = 4 / ((n + 4).factorial : ℚ) + 4 * (p.hi - p.lo) / 2 ^ j := by
      unfold radius
      ring
    _ ≤ 1 / (2 : ℚ) ^ n / 2 + (p.hi - p.lo) / 2 := add_le_add ht hangle
    _ ≤ _ := by linarith

/-- Width of the rational cosine enclosure, with a precision-certified pi interval. -/
lemma cos_enclosure_accuracy (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds)
    (hp : p.hi - p.lo ≤ 1 / (2 : ℚ) ^ n) :
    cosHi j n p - cosLo j n p ≤ 1 / (2 : ℚ) ^ n := by
  have h := radius_accuracy j n hj p hp
  simp only [cosHi, cosLo]
  linarith

/-- Width of the rational sine enclosure, with a precision-certified pi interval. -/
lemma sin_enclosure_accuracy (j n : ℕ) (hj : 3 ≤ j) (p : PiBounds)
    (hp : p.hi - p.lo ≤ 1 / (2 : ℚ) ^ n) :
    sinHi j n p - sinLo j n p ≤ 1 / (2 : ℚ) ^ n := by
  have h := radius_accuracy j n hj p hp
  simp only [sinHi, sinLo]
  linarith

private lemma pi20_accuracy (n : ℕ) (hn : n ≤ 56) :
    pi20.hi - pi20.lo ≤ 1 / (2 : ℚ) ^ n := by
  have h : pi20.hi - pi20.lo ≤ 1 / (2 : ℚ) ^ 56 := by decide +kernel
  apply h.trans
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hn

/-- The default interval supports every requested precision up to 56 bits. -/
lemma cos_default_accuracy (j n : ℕ) (hj : 3 ≤ j) (hn : n ≤ 56) :
    cosHi j n - cosLo j n ≤ 1 / (2 : ℚ) ^ n :=
  cos_enclosure_accuracy j n hj pi20 (pi20_accuracy n hn)

/-- The default interval supports every requested precision up to 56 bits. -/
lemma sin_default_accuracy (j n : ℕ) (hj : 3 ≤ j) (hn : n ≤ 56) :
    sinHi j n - sinLo j n ≤ 1 / (2 : ℚ) ^ n :=
  sin_enclosure_accuracy j n hj pi20 (pi20_accuracy n hn)

/-- A kernel-checked numerical cosine enclosure of width one billionth. -/
lemma cos_dyadic_ten_enclosed :
    (999981175 / 1000000000 : ℝ) ≤ Real.cos (2 * Real.pi / 2 ^ 10) ∧
      Real.cos (2 * Real.pi / 2 ^ 10) ≤ (999981176 / 1000000000 : ℝ) := by
  have hlo : (999981175 / 1000000000 : ℚ) ≤ cosLo 10 12 := by decide +kernel
  have hhi : cosHi 10 12 ≤ (999981176 / 1000000000 : ℚ) := by decide +kernel
  have hlo' := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhi' := (Rat.cast_le (K := ℝ)).mpr hhi
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo' hhi'
  constructor
  · have h := cosLo_le_cos 10 12 (by omega)
    linarith
  · have h := cos_le_cosHi 10 12 (by omega)
    linarith

end QuantumAlg.TrigEnclosure
