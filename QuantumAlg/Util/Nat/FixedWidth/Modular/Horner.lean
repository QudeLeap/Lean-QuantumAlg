/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Bitwise
import Lean.Elab.Tactic.Omega

/-!
# High-to-low modular Horner multiplication with a clean target

The target starts at zero. Each public bit position doubles that target and
conditionally adds the unchanged source. No source doubling or inverse
restoration is omitted: this recurrence never changes the source at all.
An arbitrary original accumulator requires a different recurrence.
-/

namespace QuantumAlg.Nat.FixedWidth.ModularHorner

/-- Appending the next low bit doubles the already read high prefix. -/
lemma highPrefix_bit (value index : Nat) :
    value / 2 ^ index =
      2 * (value / 2 ^ (index + 1)) + (value.testBit index).toNat := by
  rw [Nat.toNat_testBit]
  have split := Nat.mod_add_div (value / 2 ^ index) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at split
  change value / 2 ^ index % 2 + 2 * (value / 2 ^ (index + 1)) =
    value / 2 ^ index at split
  omega

private lemma step_mod (modulus source hornerPrefix bit : Nat) :
    (2 * ((hornerPrefix * source) % modulus) + bit * source) % modulus =
      ((2 * hornerPrefix + bit) * source) % modulus := by
  calc
    _ = (2 * (hornerPrefix * source) + bit * source) % modulus := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    _ = _ := by rw [Nat.add_mul, Nat.mul_assoc]

/-- The coordinate recurrence for a fixed high-to-low sequence of multiplier bits. -/
def hornerPrefix (modulus source multiplier width : Nat) : Nat → Nat
  | 0 => 0
  | processed + 1 =>
      (2 * hornerPrefix modulus source multiplier width processed +
        (multiplier.testBit (width - processed - 1)).toNat * source) % modulus

/-- Each prefix is the original high multiplier prefix times the unchanged source. -/
lemma prefix_eq (modulus source multiplier width processed : Nat)
    (multiplierBound : multiplier < 2 ^ width) (within : processed ≤ width) :
    hornerPrefix modulus source multiplier width processed =
      ((multiplier / 2 ^ (width - processed)) * source) % modulus := by
  induction processed with
  | zero =>
      simp only [hornerPrefix, Nat.sub_zero, Nat.div_eq_of_lt multiplierBound,
        Nat.zero_mul, Nat.zero_mod]
  | succ processed inductionHypothesis =>
      rw [hornerPrefix, inductionHypothesis (by omega)]
      have next := highPrefix_bit multiplier (width - processed - 1)
      have position : width - processed - 1 + 1 = width - processed := by omega
      rw [position] at next
      rw [show width - (processed + 1) = width - processed - 1 by omega, next]
      exact step_mod modulus source _ _

/-- A complete high-to-low scan produces the original modular product. -/
lemma prefix_full (modulus source multiplier width : Nat)
    (multiplierBound : multiplier < 2 ^ width) :
    hornerPrefix modulus source multiplier width width = (multiplier * source) % modulus := by
  simpa only [Nat.sub_self, Nat.pow_zero, Nat.div_one] using
    prefix_eq modulus source multiplier width width multiplierBound le_rfl

lemma prefix_canonical {modulus source multiplier width processed : Nat}
    (positive : 0 < modulus) (multiplierBound : multiplier < 2 ^ width)
    (within : processed ≤ width) :
    hornerPrefix modulus source multiplier width processed < modulus := by
  rw [prefix_eq modulus source multiplier width processed multiplierBound within]
  exact Nat.mod_lt _ positive

end QuantumAlg.Nat.FixedWidth.ModularHorner
