/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Analysis

/-!
# Full-grid strict phase-window tail

The geometric Fourier kernel has total squared-amplitude mass one.  At a
strict radius of half a subgroup residue and physical oversampling at least
sixteen, its bad mass is at most nine over 128.  These statements concern the
kernel; connecting it to an actual DLP point stream is a separate obligation.
-/

namespace QuantumAlg.EllipticCurve.FullRange

open scoped BigOperators

/-- The geometric Fourier kernel is the coordinate vector of a certified
inverse-Fourier state and therefore has total mass one. -/
lemma geometricAmplitude_square_sum (width : Nat) (phase : ℝ) :
    ∑ raw : Fin (2 ^ width), ‖phaseRegisterGeometricAmplitude width phase raw‖ ^ 2 = 1 := by
  have normalized := ((invQFT width).apply (phaseState width phase)).norm_eq_one
  rw [EuclideanSpace.norm_eq] at normalized
  have squared := congrArg (fun value : ℝ => value ^ 2) normalized
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), one_pow] at squared
  simpa only [invQFT_phaseState_apply_geometricSum] using squared

/-- The full-grid bad mass is bounded uniformly in the eigenphase whenever
the physical modulus is at least sixteen times the subgroup order. -/
lemma halfResidue_badMass_le (width order : Nat) (orderPositive : 0 < order)
    (oversampling : 16 * order ≤ 2 ^ width) (phase : ℝ) :
    qpeBadIndexMass width phase (1 / (2 * order)) ≤ (9 : ℝ) / 128 := by
  have orderPositiveReal : (0 : ℝ) < order := by exact_mod_cast orderPositive
  have tail := qpeBadIndexMass_le width phase (1 / (2 * order)) (by positivity)
  let scaled : ℝ := (2 : ℝ) ^ width * (1 / (2 * order))
  have scaleBound : 8 ≤ scaled := by
    have overReal : (16 : ℝ) * order ≤ (2 : ℝ) ^ width := by exact_mod_cast oversampling
    dsimp only [scaled]
    rw [mul_one_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * order)).2
    nlinarith
  have first : 1 / (2 * scaled) ≤ (1 : ℝ) / 16 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have second : 1 / (2 * scaled ^ 2) ≤ (1 : ℝ) / 128 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have expression : 1 / (2 * (2 : ℝ) ^ width * (1 / (2 * order))) +
      1 / (2 * ((2 : ℝ) ^ width * (1 / (2 * order))) ^ 2) =
      1 / (2 * scaled) + 1 / (2 * scaled ^ 2) := by dsimp [scaled]; ring
  rw [expression] at tail
  linarith

noncomputable section

/-- Geometric-kernel mass retained by a strict cyclic phase window. -/
def strictWindowMass (width : Nat) (phase radius : ℝ) : ℝ := by
  classical
  exact ∑ raw : Fin (2 ^ width),
    if qpePhaseDistance width phase raw < radius then
      ‖phaseRegisterGeometricAmplitude width phase raw‖ ^ 2 else 0

/-- Strict good windows and their closed bad complement partition the entire
physical grid, including exact boundary points. -/
lemma strictWindowMass_add_badMass (width : Nat) (phase radius : ℝ) :
    strictWindowMass width phase radius + qpeBadIndexMass width phase radius = 1 := by
  classical
  rw [strictWindowMass, qpeBadIndexMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  calc
    _ = ∑ raw : Fin (2 ^ width),
        ‖phaseRegisterGeometricAmplitude width phase raw‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro raw _
      by_cases good : qpePhaseDistance width phase raw < radius
      · simp only [good, not_le.mpr good, if_true, if_false, add_zero]
      · simp only [good, le_of_not_gt good, if_false, if_true, zero_add]
    _ = 1 := geometricAmplitude_square_sum width phase

/-- Every eigenphase retains at least 119/128 mass in its strict half-residue
window at oversampling sixteen or greater. -/
lemma halfResidue_strictWindowMass_ge (width order : Nat) (orderPositive : 0 < order)
    (oversampling : 16 * order ≤ 2 ^ width) (phase : ℝ) :
    (119 : ℝ) / 128 ≤ strictWindowMass width phase (1 / (2 * order)) := by
  have partition := strictWindowMass_add_badMass width phase (1 / (2 * order))
  have tail := halfResidue_badMass_le width order orderPositive oversampling phase
  linarith

/-- Independent Fourier factors retain at least 55/64 joint strict-window
mass, uniformly in both eigenphases. -/
lemma twoPhase_strictWindowMass_ge (width order : Nat) (orderPositive : 0 < order)
    (oversampling : 16 * order ≤ 2 ^ width) (leftPhase rightPhase : ℝ) :
    (55 : ℝ) / 64 ≤
      strictWindowMass width leftPhase (1 / (2 * order)) *
        strictWindowMass width rightPhase (1 / (2 * order)) := by
  have left := halfResidue_strictWindowMass_ge width order orderPositive oversampling leftPhase
  have right := halfResidue_strictWindowMass_ge width order orderPositive oversampling rightPhase
  calc
    (55 : ℝ) / 64 ≤ (119 / 128 : ℝ) * (119 / 128) := by norm_num
    _ ≤ _ := mul_le_mul left right (by norm_num) (by linarith)

end

end QuantumAlg.EllipticCurve.FullRange
