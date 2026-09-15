/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ClassicalOp
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Group.Nat.Even

/-!
# Exact parity of the actual least-significant order bit

The structural word index is big endian. Its last physical bit is therefore
the numerical bit zero, and the existing native NOT instruction produces the
ordinary evenness decision. This identity covers every stored word.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

private theorem not_testBit_zero (value : Nat) :
    Bool.not (value.testBit 0) = decide (Even value) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  by_cases even : Even value
  · have remainder : value % 2 = 0 := Nat.even_iff.mp even
    simp [remainder, even]
  · have remainder : value % 2 = 1 := by
      have nonzero : value % 2 ≠ 0 := fun zero => even (Nat.even_iff.mpr zero)
      have bounded : value % 2 < 2 := Nat.mod_lt value (by decide)
      omega
    simp [remainder, even]

/-- The real NOT on the stored word's last bit computes exact natural evenness. -/
theorem evenOrder_eval {width : Nat} (value : CShape.Word (width + 1)) :
    (Resource.BitOpcode.eval .not (value.wordBitGet (Fin.last width))).toBool =
      decide (Even value.toNat) := by
  cases value with
  | unsignedWord value =>
    change Bool.not (value.val.testBit (width + 1 - 1 - width)) = decide (Even value.val)
    rw [Nat.add_sub_cancel, Nat.sub_self]
    exact not_testBit_zero value.val

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
