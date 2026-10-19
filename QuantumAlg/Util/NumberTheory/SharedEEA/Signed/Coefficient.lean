/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Quotient.Bits
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Packing

/-!
# Actual signed coefficient-window instructions

The source swaps the next quotient bit into `Sign`, conditionally subtracts
the coefficient when that bit is zero, complements `Sign`, and adds the
coefficient to the complete sign/window word
[LYL+26, sec_EEA/sub_regshare.tex:288-296]. This module executes those exact
`BitVec` operations. The zero-bit branch uses modular signed wraparound;
the one-bit branch performs the actual bounded addition. Both branches
clear the high sign bit and leave the consumed quotient position zero.

The aligned integer window is below the coefficient. Its declared source
width has room for the sum. Those are internal reachable-window properties,
to be obtained from the actual coefficient phase and its prescribed
`ℓ_t + 1` arithmetic region. The comparison used to recover the consumed
bit is weak: equality correctly recovers one, including a zero old window.
No assumption that the full coefficient is divisible by its scale is made.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SignedCoefficient

variable {width : Nat}

/-- Execute conditional modular subtraction, Sign complement, and complete signed-word addition. -/
def addBit (value coefficient : BitVec width) (digit : Bool) : BitVec (width + 1) :=
  let reduced := if digit then value else value - coefficient
  BitVec.cons (!digit) reduced + coefficient.setWidth (width + 1)

/-- The actual signed instructions return the prescribed coefficient contribution numerically. -/
lemma addBit_toNat (value coefficient : BitVec width) (digit : Bool)
    (below : value.toNat < coefficient.toNat)
    (room : value.toNat + coefficient.toNat < 2 ^ width) :
    (addBit value coefficient digit).toNat =
      value.toNat + if digit then coefficient.toNat else 0 := by
  have coefficientNat : (coefficient.setWidth (width + 1)).toNat = coefficient.toNat :=
    BitVec.toNat_setWidth_of_le (by omega)
  have valueBound := value.isLt
  have coefficientBound := coefficient.isLt
  cases digit with
  | false =>
    have ordered : value < coefficient := by simpa only [BitVec.lt_def] using below
    change (BitVec.cons true (value - coefficient) +
      coefficient.setWidth (width + 1)).toNat = value.toNat + 0
    rw [BitVec.toNat_add, BitVec.toNat_cons', BitVec.toNat_sub_of_lt ordered, coefficientNat]
    simp only [Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul, Nat.add_zero]
    have wrapped : 2 ^ width + (2 ^ width - (coefficient.toNat - value.toNat)) +
        coefficient.toNat = 2 ^ (width + 1) + value.toNat := by
      rw [Nat.pow_succ]
      omega
    rw [wrapped, Nat.add_mod_left, Nat.mod_eq_of_lt]
    exact valueBound.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  | true =>
    change (BitVec.cons false value + coefficient.setWidth (width + 1)).toNat =
      value.toNat + coefficient.toNat
    rw [BitVec.toNat_add, BitVec.toNat_cons', coefficientNat]
    simp only [Bool.toNat_false, Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mod_eq_of_lt]
    exact room.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

/-- The concrete signed result fits below the sign bit in both quotient branches. -/
lemma addBit_fits (value coefficient : BitVec width) (digit : Bool)
    (below : value.toNat < coefficient.toNat)
    (room : value.toNat + coefficient.toNat < 2 ^ width) :
    (addBit value coefficient digit).toNat < 2 ^ width := by
  rw [addBit_toNat value coefficient digit below room]
  cases digit with
  | false => simpa only [Bool.false_eq_true, if_false, Nat.add_zero] using value.isLt
  | true => exact room

/-- The signed addition clears the high Sign bit, including its wraparound branch. -/
lemma addBit_sign (value coefficient : BitVec width) (digit : Bool)
    (below : value.toNat < coefficient.toNat)
    (room : value.toNat + coefficient.toNat < 2 ^ width) :
    (addBit value coefficient digit).msb = false := by
  rw [BitVec.msb_eq_decide, Nat.add_sub_cancel]
  have fits := addBit_fits value coefficient digit below room
  simp only [Nat.not_le.mpr fits, decide_false]

/-- The actual integer window extracted after addition is the intended, untruncated contribution. -/
lemma addBit_low (value coefficient : BitVec width) (digit : Bool)
    (below : value.toNat < coefficient.toNat)
    (room : value.toNat + coefficient.toNat < 2 ^ width) :
    ((addBit value coefficient digit).setWidth width).toNat =
      value.toNat + if digit then coefficient.toNat else 0 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (addBit_fits value coefficient digit below room)]
  exact addBit_toNat value coefficient digit below room

/-- The updated word recovers the consumed quotient bit through the actual weak comparison. -/
lemma addBit_recover_digit (value coefficient : BitVec width) (digit : Bool)
    (below : value.toNat < coefficient.toNat)
    (room : value.toNat + coefficient.toNat < 2 ^ width) :
    QuotientBits.readBit coefficient.toNat
      ((addBit value coefficient digit).setWidth width).toNat = digit := by
  rw [addBit_low value coefficient digit below room]
  exact QuotientBits.readBit_add coefficient.toNat value.toNat digit below

/-- Reconstruct the old window and consumed bit directly from the actual updated low word. -/
def rewind (coefficient output : BitVec width) : BitVec width × Bool :=
  let digit := QuotientBits.readBit coefficient.toNat output.toNat
  (if digit then output - coefficient else output, digit)

/-- The updated arithmetic window restores the old window and the consumed quotient bit. -/
lemma rewind_addBit (value coefficient : BitVec width) (digit : Bool)
    (below : value.toNat < coefficient.toNat)
    (room : value.toNat + coefficient.toNat < 2 ^ width) :
    rewind coefficient ((addBit value coefficient digit).setWidth width) = (value, digit) := by
  have recovered := addBit_recover_digit value coefficient digit below room
  apply Prod.ext
  · dsimp only [rewind]
    rw [recovered]
    apply BitVec.eq_of_toNat_eq
    cases digit with
    | false =>
      simp only [Bool.false_eq_true, if_false, addBit_low value coefficient false below room,
        Nat.add_zero]
    | true =>
      change (((addBit value coefficient true).setWidth width) - coefficient).toNat = value.toNat
      have low := addBit_low value coefficient true below room
      change ((addBit value coefficient true).setWidth width).toNat =
        value.toNat + coefficient.toNat at low
      have selected : coefficient ≤ (addBit value coefficient true).setWidth width := by
        rw [BitVec.le_def, low]
        omega
      rw [BitVec.toNat_sub_of_le selected, low]
      change value.toNat + coefficient.toNat - coefficient.toNat = value.toNat
      omega
  · exact recovered

/-- Equality of actual updated low words preserves both reachable inputs and consumed digits. -/
lemma addBit_low_injective (coefficient : BitVec width)
    {left right : BitVec width} {leftDigit rightDigit : Bool}
    (leftBelow : left.toNat < coefficient.toNat)
    (rightBelow : right.toNat < coefficient.toNat)
    (leftRoom : left.toNat + coefficient.toNat < 2 ^ width)
    (rightRoom : right.toNat + coefficient.toNat < 2 ^ width)
    (same : (addBit left coefficient leftDigit).setWidth width =
      (addBit right coefficient rightDigit).setWidth width) :
    (left, leftDigit) = (right, rightDigit) := by
  calc
    (left, leftDigit) = rewind coefficient ((addBit left coefficient leftDigit).setWidth width) :=
      (rewind_addBit left coefficient leftDigit leftBelow leftRoom).symm
    _ = rewind coefficient ((addBit right coefficient rightDigit).setWidth width) :=
      congrArg (rewind coefficient) same
    _ = (right, rightDigit) := rewind_addBit right coefficient rightDigit rightBelow rightRoom

/-- The smallest window exercises actual signed wraparound and equality recovery. -/
lemma smallest_window_branches :
    addBit (0 : BitVec 2) (1 : BitVec 2) false = (0 : BitVec 3) ∧
      addBit (0 : BitVec 2) (1 : BitVec 2) true = (1 : BitVec 3) ∧
      rewind (1 : BitVec 2) (1 : BitVec 2) = ((0 : BitVec 2), true) := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.SignedCoefficient
