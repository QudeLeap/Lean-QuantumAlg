/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-!
# Finite cyclic character transforms and fiber amplitudes

The cyclic group dimension is arbitrary and independent of any physical
power-of-two register.  Character orthogonality gives exact Parseval and
pushforward identities for complex amplitudes, without a truncation of the
source labels.
-/

namespace QuantumAlg.CyclicFourier

open AddChar
open scoped BigOperators

noncomputable section

variable {order : Nat} [NeZero order]

/-- The positive-sign cyclic character transform. -/
def transform (value : ZMod order → ℂ) (frequency : ZMod order) : ℂ :=
  ∑ label : ZMod order, ZMod.stdAddChar (frequency * label) * value label

/-- Orthogonality of the full cyclic character family. -/
lemma character_sum (residue : ZMod order) :
    ∑ frequency : ZMod order, ZMod.stdAddChar (residue * frequency) =
      if residue = 0 then (order : ℂ) else 0 := by
  classical
  split_ifs with zero
  · simp only [zero, zero_mul, map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar order zero)

private lemma star_character (label : ZMod order) :
    star (ZMod.stdAddChar label) = ZMod.stdAddChar (-label) := by
  simpa only [Complex.star_def] using (AddChar.map_neg_eq_conj ZMod.stdAddChar label).symm

/-- Parseval as an exact complex correlation identity for the arbitrary cyclic group. -/
lemma transform_correlation (left right : ZMod order → ℂ) :
    ∑ frequency : ZMod order,
        transform left frequency * star (transform right frequency) =
      (order : ℂ) * ∑ label : ZMod order, left label * star (right label) := by
  classical
  calc
    _ = ∑ frequency : ZMod order, ∑ a : ZMod order, ∑ b : ZMod order,
        ZMod.stdAddChar ((a - b) * frequency) * (left a * star (right b)) := by
      simp only [transform, star_sum, star_mul, star_character, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [show (a - b) * frequency = frequency * a + -(frequency * b) by ring,
        map_add_eq_mul]
      ring
    _ = ∑ a : ZMod order, ∑ b : ZMod order,
        (∑ frequency : ZMod order, ZMod.stdAddChar ((a - b) * frequency)) *
          (left a * star (right b)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
    _ = _ := by
      simp only [character_sum, sub_eq_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.mul_sum]

/-- Full cyclic Parseval converts fiber Born mass into the uniform character mixture. -/
lemma transform_square_sum (value : ZMod order → ℂ) :
    ∑ frequency : ZMod order, ‖transform value frequency‖ ^ 2 =
      (order : ℝ) * ∑ label : ZMod order, ‖value label‖ ^ 2 := by
  have correlation := congrArg Complex.re (transform_correlation value value)
  simpa only [Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq] using correlation

/-- The exact complex fiber amplitude obtained by evaluating a source label. -/
def fiberAmplitude {Source : Type*} [Fintype Source]
    (label : Source → ZMod order) (amplitude : Source → ℂ) (output : ZMod order) : ℂ := by
  classical
  exact ∑ source : Source, if label source = output then amplitude source else 0

/-- Transforming actual evaluation fibers is exactly the character-weighted
source sum.  No divisibility relation between source and group cardinalities is required. -/
lemma transform_fiberAmplitude {Source : Type*} [Fintype Source]
    (label : Source → ZMod order) (amplitude : Source → ℂ) (frequency : ZMod order) :
    transform (fiberAmplitude label amplitude) frequency =
      ∑ source : Source, ZMod.stdAddChar (frequency * label source) * amplitude source := by
  classical
  simp only [transform, fiberAmplitude, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The transformed fiber of an affine two-register evaluation factors into
its two full source sums.  The seed contributes one common character phase. -/
lemma transform_pair_fiberAmplitude {Left Right : Type*} [Fintype Left] [Fintype Right]
    (seed : ZMod order) (leftLabel : Left → ZMod order) (rightLabel : Right → ZMod order)
    (leftAmplitude : Left → ℂ) (rightAmplitude : Right → ℂ) (frequency : ZMod order) :
    transform (fiberAmplitude
      (fun source : Left × Right => seed + leftLabel source.1 + rightLabel source.2)
      (fun source => leftAmplitude source.1 * rightAmplitude source.2)) frequency =
      ZMod.stdAddChar (frequency * seed) *
        (∑ left : Left, ZMod.stdAddChar (frequency * leftLabel left) * leftAmplitude left) *
        (∑ right : Right, ZMod.stdAddChar (frequency * rightLabel right) *
          rightAmplitude right) := by
  rw [transform_fiberAmplitude, Fintype.sum_prod_type, mul_assoc, Finset.sum_mul_sum]
  simp only [mul_add, map_add_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

/-- The full fiber Born mass is the exact uniform cyclic-character mixture
of two Fourier factors.  The seed phase disappears, and the source cardinality
need not be the group order or a multiple of it. -/
lemma pair_fiberAmplitude_square_sum {Left Right : Type*} [Fintype Left] [Fintype Right]
    (seed : ZMod order) (leftLabel : Left → ZMod order) (rightLabel : Right → ZMod order)
    (leftAmplitude : Left → ℂ) (rightAmplitude : Right → ℂ) :
    (∑ output : ZMod order, ‖fiberAmplitude
      (fun source : Left × Right => seed + leftLabel source.1 + rightLabel source.2)
      (fun source => leftAmplitude source.1 * rightAmplitude source.2) output‖ ^ 2) =
      (order : ℝ)⁻¹ * ∑ frequency : ZMod order,
        ‖∑ left : Left, ZMod.stdAddChar (frequency * leftLabel left) * leftAmplitude left‖ ^ 2 *
        ‖∑ right : Right, ZMod.stdAddChar (frequency * rightLabel right) *
          rightAmplitude right‖ ^ 2 := by
  let fiber := fiberAmplitude
    (fun source : Left × Right => seed + leftLabel source.1 + rightLabel source.2)
    (fun source => leftAmplitude source.1 * rightAmplitude source.2)
  have parseval := transform_square_sum fiber
  have factor (frequency : ZMod order) :
      ‖transform fiber frequency‖ ^ 2 =
        ‖∑ left : Left, ZMod.stdAddChar (frequency * leftLabel left) * leftAmplitude left‖ ^ 2 *
        ‖∑ right : Right, ZMod.stdAddChar (frequency * rightLabel right) *
          rightAmplitude right‖ ^ 2 := by
    rw [show fiber = _ from rfl, transform_pair_fiberAmplitude, norm_mul, norm_mul,
      AddChar.norm_apply, one_mul, mul_pow]
  simp_rw [factor] at parseval
  have orderNonzero : (order : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne order
  calc
    _ = (order : ℝ)⁻¹ * ((order : ℝ) * ∑ output : ZMod order, ‖fiber output‖ ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ orderNonzero, one_mul]
    _ = _ := by rw [← parseval]

end

end QuantumAlg.CyclicFourier
