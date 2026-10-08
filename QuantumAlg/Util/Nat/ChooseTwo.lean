/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.Nat.Choose.Basic
import all Mathlib.Data.Nat.Choose.Basic
import all Mathlib.Tactic.Ring

/-!
# Weighted two-element selection

The exact pair count can be expressed either as a binomial coefficient or as
the product of a width and its predecessor.
-/

namespace QuantumAlg.ChooseTwo

/-- Convert the two actual inverse-QFT pair counts to their weighted product formula. -/
public theorem weighted_choose_two_sum (count first second : Nat) :
    16 * count * (_root_.Nat.choose first 2 + _root_.Nat.choose second 2) =
      8 * count * (first * (first - 1) + second * (second - 1)) := by
  have firstEq := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self first)
  have secondEq := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self second)
  rw [Nat.choose_two_right, Nat.choose_two_right]
  have halfSum : 2 * (first * (first - 1) / 2 + second * (second - 1) / 2) =
      first * (first - 1) + second * (second - 1) := by omega
  calc
    _ = 8 * count * (2 * (first * (first - 1) / 2 + second * (second - 1) / 2)) := by ring
    _ = _ := congrArg (8 * count * ·) halfSum

end QuantumAlg.ChooseTwo
