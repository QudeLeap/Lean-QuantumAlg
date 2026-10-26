/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address
import Mathlib.Data.BitVec

/-!
# Complete MSB-first selector decoding agrees with the original binary word

The interval decoder reads every original address position. This bridge
retains the full word width, including zero width, and identifies its result
with the original fixed-width binary value rather than a truncated label.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma mod_two_pow_succ_bit (number remaining : Nat) :
    number % 2 ^ (remaining + 1) =
      (if number.testBit remaining then 2 ^ remaining else 0) + number % 2 ^ remaining := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (number / 2 ^ remaining) with zero | one
  · simp [zero]
  · simp [one, Nat.add_comm]

/-- The remaining binary interval contributes exactly the original word's low remaining bits. -/
lemma addressLabelAt_val_bitVec (frame : SelectorFrame encoding width)
    (word : BitVec width) (state : Data)
    (addressBits : ∀ index, (frame.address index).get state = word.getMsbD index.val)
    (remaining depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    (frame.addressLabelAt remaining depth fits offset bounded state).val =
      offset + word.toNat % 2 ^ remaining := by
  induction remaining generalizing depth offset with
  | zero => simp only [addressLabelAt, pow_zero, Nat.mod_one, Nat.add_zero]
  | succ remaining ih =>
      have present : depth < width := by omega
      have read : (frame.addressAt depth present).get state = word.toNat.testBit remaining := by
        change (frame.address ⟨depth, present⟩).get state = _
        rw [addressBits, BitVec.getMsbD_eq_getLsbD]
        simp only [present, decide_true, Bool.true_and]
        rw [show width - 1 - depth = remaining by omega]
        rfl
      dsimp only [addressLabelAt]
      rw [read]
      split
      next chosen =>
        rw [ih, mod_two_pow_succ_bit, if_pos chosen]
        omega
      next chosen =>
        rw [ih, mod_two_pow_succ_bit, if_neg chosen]
        omega

/-- Reading the complete original MSB-first word returns exactly that word's finite value. -/
lemma addressLabelAt_bitVec (frame : SelectorFrame encoding width)
    (word : BitVec width) (state : Data)
    (addressBits : ∀ index, (frame.address index).get state = word.getMsbD index.val) :
    frame.addressLabelAt width 0 (by omega) 0 (by omega) state = word.toFin := by
  apply Fin.ext
  rw [frame.addressLabelAt_val_bitVec word state addressBits]
  change 0 + word.toNat % 2 ^ width = word.toNat
  rw [Nat.mod_eq_of_lt word.isLt, Nat.zero_add]

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
