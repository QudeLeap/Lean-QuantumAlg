/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.Binary.Arithmetic
import Mathlib.Data.BitVec

/-!
# Finite-word carry characterization of a controlled positive threshold comparison

For a positive static threshold, adding its finite-word negative produces
carry exactly on the complementary greater-or-equal branch. Xoring the
original active control leaves strict less-than. This comparison is a
project derivation using the native carry construction
[G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction

variable {width : Nat}

/-- The static finite-word negative of a positive threshold is its exact capacity complement. -/
lemma comparisonOffset_nat (threshold : BitVec width) (positive : 0 < threshold.toNat) :
    (-threshold).toNat = 2 ^ width - threshold.toNat := by
  apply BitVec.toNat_neg_of_pos
  change 0 < threshold.toNat
  exact positive

/-- The actual selected offset's outgoing carry, xored with control, is strict comparison. -/
lemma comparisonCarry_below (threshold input : BitVec width) (positive : 0 < threshold.toNat)
    (active : Bool) :
    (Nat.BinaryArithmetic.natAddCarry input.toNat
      (if active then (-threshold).toNat else 0) width ^^ active) =
        (active && decide (input.toNat < threshold.toNat)) := by
  cases active with
  | false =>
      change (Nat.BinaryArithmetic.natAddCarry input.toNat 0 width ^^ false) = false
      rw [Nat.BinaryArithmetic.natAddCarry_eq_decide_two_pow_le input.isLt
        (Nat.two_pow_pos width), decide_eq_false (by have bounded := input.isLt; omega)]
      rfl
  | true =>
      change (Nat.BinaryArithmetic.natAddCarry input.toNat (-threshold).toNat width ^^ true) =
        decide (input.toNat < threshold.toNat)
      rw [Nat.BinaryArithmetic.natAddCarry_eq_decide_two_pow_le input.isLt (-threshold).isLt,
        comparisonOffset_nat threshold positive]
      by_cases below : input.toNat < threshold.toNat
      · rw [decide_eq_true below, decide_eq_false (by
          have thresholdBound := threshold.isLt
          omega : ¬ 2 ^ width ≤ input.toNat + (2 ^ width - threshold.toNat))]
        rfl
      · rw [decide_eq_false below, decide_eq_true (by
          have thresholdBound := threshold.isLt
          omega : 2 ^ width ≤ input.toNat + (2 ^ width - threshold.toNat))]
        rfl

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction
