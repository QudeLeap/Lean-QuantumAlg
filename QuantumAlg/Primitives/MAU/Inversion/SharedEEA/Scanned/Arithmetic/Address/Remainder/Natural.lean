/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Remainder

/-!
# Untruncated remainder addresses on admitted positive windows

The positive-window predicate is the complete finite metadata test, not
a reachable-trajectory promise. Actual zero padding and address zero
identify the executed native subtractions with the original natural
length minus one. Invalid finite labels retain their modular semantics
from the imported owner and are excluded only by the actual guard.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The actual physical X load fits even at the smallest admitted positive width. -/
lemma remainderConstant_toNat (width : Nat) (positive : 1 ≤ width) :
    (remainderConstant width).toNat = width + 3 - 2 := by
  exact Nat.mod_eq_of_lt
    (ScanMetadata.targetIndex_lt width positive ⟨width + 3 - 2, by omega⟩)

/-- Actual native address preparation gives the full natural window length minus one. -/
lemma remainderStep_address_toNat (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
      state.1.shift.toNat < width + 3) :
    (remainderStep width positive state).2.1.toNat =
      width + 3 - 2 - state.1.coefficientLength.toNat - state.1.quotientLength.toNat -
        state.1.shift.toNat := by
  have constant := remainderConstant_toNat width positive
  have coefficient := sourceValue_toNat_of_prefix_zero width positive .coefficient state clean
  have quotient := sourceValue_toNat_of_prefix_zero width positive .quotient state clean
  have shift := sourceValue_toNat_of_prefix_zero width positive .shift state clean
  change (sourceValue width positive .coefficient state).toNat =
    state.1.coefficientLength.toNat at coefficient
  change (sourceValue width positive .quotient state).toNat =
    state.1.quotientLength.toNat at quotient
  change (sourceValue width positive .shift state).toNat = state.1.shift.toNat at shift
  have first : (remainderConstant width - sourceValue width positive .coefficient state).toNat =
      width + 3 - 2 - state.1.coefficientLength.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), constant, coefficient]
  have second : (remainderConstant width - sourceValue width positive .coefficient state -
      sourceValue width positive .quotient state).toNat =
      width + 3 - 2 - state.1.coefficientLength.toNat - state.1.quotientLength.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), first, quotient]
  rw [remainderStep_address, zero, BitVec.zero_xor,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), second, shift]

/-- The same physical address is a valid index into the unchanged original work word. -/
lemma remainderStep_address_lt (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
      state.1.shift.toNat < width + 3) :
    (remainderStep width positive state).2.1.toNat < width + 3 := by
  rw [remainderStep_address_toNat width positive state clean zero enabled]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
