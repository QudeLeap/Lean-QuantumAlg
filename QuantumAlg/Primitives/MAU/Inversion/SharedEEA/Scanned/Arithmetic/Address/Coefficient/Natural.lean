/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient.Runtime

/-!
# Complete natural coefficient addresses from the actual phase-controlled circuit

Original Phase2 selects the executed native word. The full finite
positive-window predicate discharges natural subtraction without any
trajectory restriction. All other labels keep their complete modular
action. The physical prefix and separate conjunction remain intact.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The phase-four native X load fits the actual address at every positive width. -/
lemma coefficientConstant_toNat (width : Nat) (positive : 1 ≤ width) :
    (coefficientConstant width).toNat = width + 3 - 1 := by
  exact Nat.mod_eq_of_lt
    (ScanMetadata.targetIndex_lt width positive ⟨width + 3 - 1, by omega⟩)

/-- Each actual fixed-phase address is the full admitted source length minus one. -/
lemma coefficientStep_address_toNat (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : if deshift then state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
      else state.1.coefficientLength.toNat + 1 ≤ width + 3) :
    (coefficientStep width positive deshift state).2.1.toNat =
      if deshift then width + 3 - 1 - state.1.divisorLength.toNat - state.1.shift.toNat
      else state.1.coefficientLength.toNat := by
  have coefficient := sourceValue_toNat_of_prefix_zero width positive .coefficient state clean
  have divisor := sourceValue_toNat_of_prefix_zero width positive .divisor state clean
  have shift := sourceValue_toNat_of_prefix_zero width positive .shift state clean
  change (sourceValue width positive .coefficient state).toNat =
    state.1.coefficientLength.toNat at coefficient
  change (sourceValue width positive .divisor state).toNat =
    state.1.divisorLength.toNat at divisor
  change (sourceValue width positive .shift state).toNat = state.1.shift.toNat at shift
  rw [coefficientStep_address, zero]
  cases deshift with
  | false => simpa only [Bool.false_eq_true, if_false, BitVec.add_zero] using coefficient
  | true =>
      simp only [if_true, BitVec.zero_xor] at enabled ⊢
      have constant := coefficientConstant_toNat width positive
      have first : (coefficientConstant width - sourceValue width positive .divisor state).toNat =
          width + 3 - 1 - state.1.divisorLength.toNat := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), constant, divisor]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), first, shift]

/-- The actual quantum phase chooses exactly the original natural coefficient address. -/
lemma runtimeCoefficientStep_address_toNat (width : Nat) (positive : 1 ≤ width)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : if state.1.flags.second then
      state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
      else state.1.coefficientLength.toNat + 1 ≤ width + 3) :
    (runtimeCoefficientStep width positive state).2.1.toNat =
      if state.1.flags.second then
        width + 3 - 1 - state.1.divisorLength.toNat - state.1.shift.toNat
      else state.1.coefficientLength.toNat := by
  unfold runtimeCoefficientStep
  split_ifs at enabled ⊢ with selected
  · exact coefficientStep_address_toNat width positive true state clean zero enabled
  · exact coefficientStep_address_toNat width positive false state clean zero enabled

/-- Every admitted complete finite source label fits the unchanged physical work word. -/
lemma runtimeCoefficientStep_address_lt (width : Nat) (positive : 1 ≤ width)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : if state.1.flags.second then
      state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
      else state.1.coefficientLength.toNat + 1 ≤ width + 3) :
    (runtimeCoefficientStep width positive state).2.1.toNat < width + 3 := by
  rw [runtimeCoefficientStep_address_toNat width positive state clean zero enabled]
  split_ifs at enabled ⊢ <;> omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
