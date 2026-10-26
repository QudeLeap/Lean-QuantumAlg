/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Nearest residue recovery from a strict periodic phase window

The integer lift includes both signs and modular wrap.  Strict windows exclude
half-integer ties.  The natural-number realization adds half of an even
denominator before exact unsigned division and then reduces modulo the order.
-/

namespace QuantumAlg.NearestResidue

/-- Exact unsigned nearest-integer division for a positive even denominator. -/
def quotient (numerator denominator : Nat) : Nat :=
  (numerator + denominator / 2) / denominator

/-- Adding the half denominator implements the same nearest-integer rule as
mathematical rounding when the denominator is positive and even. -/
lemma quotient_eq_round (numerator denominator : Nat)
    (positive : 0 < denominator) (even : 2 * (denominator / 2) = denominator) :
    (quotient numerator denominator : Int) = round ((numerator : ℝ) / denominator) := by
  have nonzero : (denominator : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have evenReal : (2 : ℝ) * (denominator / 2 : Nat) = denominator := by exact_mod_cast even
  have shift : (numerator : ℝ) / denominator + 1 / 2 =
      ((numerator + denominator / 2 : Nat) : ℝ) / denominator := by
    push_cast
    field_simp
    nlinarith
  rw [round_eq, shift, Int.floor_div_natCast, Int.floor_natCast]
  exact Int.natCast_ediv _ _

/-- A strict periodic phase window selects exactly its signed integer lift.
The integer `period` records all possible wrap directions. -/
lemma round_scaled_eq_of_strict_window (raw modulus order : Nat)
    (orderPositive : 0 < order) (modulusPositive : 0 < modulus)
    (residue period : Int)
    (window : |(residue : ℝ) / order - (raw : ℝ) / modulus - period| <
      1 / (2 * order)) :
    round ((raw : ℝ) * order / modulus) = residue - period * order := by
  have orderPositiveReal : (0 : ℝ) < order := by exact_mod_cast orderPositive
  have modulusNonzero : (modulus : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt modulusPositive
  have distance : |(raw : ℝ) * order / modulus -
      ((residue - period * order : Int) : ℝ)| < 1 / 2 := by
    calc
      _ = (order : ℝ) *
          |(residue : ℝ) / order - (raw : ℝ) / modulus - period| := by
        calc
          _ = |-(order : ℝ) *
              ((residue : ℝ) / order - (raw : ℝ) / modulus - period)| := by
            congr 1
            push_cast
            field_simp
            ring
          _ = _ := by rw [abs_mul, abs_neg, abs_of_pos orderPositiveReal]
      _ < (order : ℝ) * (1 / (2 * order)) :=
        mul_lt_mul_of_pos_left window orderPositiveReal
      _ = 1 / 2 := by field_simp
  apply round_eq_iff.mpr
  have inequalities := abs_lt.mp distance
  constructor <;> linarith

/-- Exact nearest division returns the intended residue after modular wrap,
including a negative phase lift. -/
lemma quotient_mod_eq_of_strict_window (raw modulus order residue : Nat)
    (orderPositive : 0 < order) (modulusPositive : 0 < modulus)
    (even : 2 * (modulus / 2) = modulus) (belowOrder : residue < order) (period : Int)
    (window : |(residue : ℝ) / order - (raw : ℝ) / modulus - period| <
      1 / (2 * order)) :
    quotient (raw * order) modulus % order = residue := by
  have lifted := round_scaled_eq_of_strict_window raw modulus order orderPositive
    modulusPositive residue period window
  rw [← Nat.cast_mul, ← quotient_eq_round (raw * order) modulus modulusPositive even] at lifted
  have residueEq := congrArg (fun value : Int => value % order) lifted
  rw [mul_comm period (order : Int), Int.sub_mul_emod_self_left,
    Int.emod_eq_of_lt (Int.natCast_nonneg residue)
    (by exact_mod_cast belowOrder)] at residueEq
  exact_mod_cast residueEq

/-- Rounding the complete unsigned product fits the existing combined width.
This is a bound on the actual addition before division, not only its quotient. -/
lemma rounded_numerator_lt (width raw order : Nat) (rawBound : raw < 2 ^ width)
    (orderBound : order ≤ 2 ^ width) :
    raw * order + 2 ^ width / 2 < 2 ^ (width + (width + 1)) := by
  have qPositive := Nat.two_pow_pos width
  have rawNext : raw + 1 ≤ 2 ^ width := rawBound
  have product : (raw + 1) * order ≤ (2 ^ width) * (2 ^ width) :=
    Nat.mul_le_mul rawNext orderBound
  have halfBound : 2 ^ width / 2 < 2 ^ width := Nat.div_lt_self qPositive (by norm_num)
  have rawProduct : raw * order ≤ raw * (2 ^ width) := Nat.mul_le_mul_left raw orderBound
  have nextProduct := Nat.mul_le_mul_right (2 ^ width) rawNext
  rw [pow_add, pow_succ]
  nlinarith

end QuantumAlg.NearestResidue
