/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Suffix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix.Readout

/-! # Original target-low-bit control and complete target-word readout -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

/-- The actual low target bit, rather than a separate reduction flag. -/
def targetLow : EncodedBit encoding := targetBit ⟨0, by decide⟩

private lemma target_wire (length : Nat) (fits : length < width) (index : Fin length) :
    (evenSuffixSubsystem length fits).wires
        (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.rightBit length index)).wire =
      (targetBit (ModularAddition.highIndex length fits.le index)).wire := by
  apply Fin.ext
  change (if length + (length - 1 - index.val) < length then _
    else if length + (length - 1 - index.val) < length + length then _ else _) = _
  have bounded := index.isLt
  rw [if_neg (by omega), if_pos (by omega)]
  change width + (length + (length - 1 - index.val) - length) =
    width + (width - 1 - (width - length + index.val))
  omega

private lemma control_wire (length : Nat) (fits : length < width) :
    (evenSuffixSubsystem length fits).wires (MAU.Addition.TTK.overflowBit length).wire =
      targetLow.wire := by
  apply Fin.ext
  change (if length + length < length then _
    else if length + length < length + length then _ else _) =
      width + (width - 1 - 0)
  rw [if_neg (by omega), if_neg (by omega)]
  omega

lemma evenSuffix_grouped_target (length : Nat) (fits : length < width) (state : Registers) :
    (((evenSuffixSubsystem length fits).full (ModularAddition.source_onto length)
      encoding_onto).grouping state).1.1.2 = highWord length fits.le state.1.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have read := (evenSuffixSubsystem length fits).full_source_read
    (ModularAddition.source_onto length) encoding_onto
    (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.rightBit length index))
    (targetBit (ModularAddition.highIndex length fits.le index))
    (target_wire length fits index) state
  simpa only [MAU.Addition.TTK.ttkWithOverflowBit_get,
    MAU.Addition.TTK.ttkRightBit_get, targetBit, ModularAddition.highIndex, highWord,
    Nat.testBit_div_two_pow, Nat.add_comm] using read

lemma evenSuffix_grouped_control (length : Nat) (fits : length < width) (state : Registers) :
    (((evenSuffixSubsystem length fits).full (ModularAddition.source_onto length)
      encoding_onto).grouping state).1.2 = targetLow.get state :=
  (evenSuffixSubsystem length fits).full_source_read (ModularAddition.source_onto length)
    encoding_onto (MAU.Addition.TTK.overflowBit length) targetLow
    (control_wire length fits) state

/-- The control within the actual target word is retained by every native instruction block. -/
lemma evenSuffix_control (length : Nat) (fits : length < width) (state : Registers) :
    targetLow.get (evenSuffixStep length fits state) = targetLow.get state := by
  have after := (evenSuffixSubsystem length fits).full_step_source_read
    (ModularAddition.source_onto length) encoding_onto
    (MAU.Addition.TTK.overflowBit length) targetLow (control_wire length fits)
    MAU.Addition.HRS.controlledBorrowedIncrementOutput state
  have before := evenSuffix_grouped_control length fits state
  change targetLow.get (evenSuffixStep length fits state) =
    (MAU.Addition.HRS.controlledBorrowedIncrementOutput _).2 at after
  have restored : ∀ original : MAU.Addition.TTK.OverflowRegisters length,
      (MAU.Addition.HRS.controlledBorrowedIncrementOutput original).2 = original.2 := by
    intro original
    dsimp only [MAU.Addition.HRS.controlledBorrowedIncrementOutput]
    split <;> rfl
  exact after.trans ((restored _).trans before)

lemma evenSuffix_high (length : Nat) (fits : length < width) (state : Registers) :
    highWord length fits.le (evenSuffixStep length fits state).1.2 =
      if targetLow.get state then
        Nat.FixedWidth.wordIncrement length (highWord length fits.le state.1.2)
      else highWord length fits.le state.1.2 := by
  let grouped := ((evenSuffixSubsystem length fits).full (ModularAddition.source_onto length)
    encoding_onto).grouping state
  have after := evenSuffix_grouped_target length fits (evenSuffixStep length fits state)
  have action :
      (((evenSuffixSubsystem length fits).full (ModularAddition.source_onto length)
        encoding_onto).grouping (evenSuffixStep length fits state)).1 =
          MAU.Addition.HRS.controlledBorrowedIncrementOutput grouped.1 := by
    simp only [evenSuffixStep, FullPlacement.step, Equiv.apply_symm_apply, grouped]
  rw [← after, action]
  have control := evenSuffix_grouped_control length fits state
  have target := evenSuffix_grouped_target length fits state
  change grouped.1.2 = targetLow.get state at control
  change grouped.1.1.2 = highWord length fits.le state.1.2 at target
  dsimp only [MAU.Addition.HRS.controlledBorrowedIncrementOutput]
  rw [control]
  cases selected : targetLow.get state <;>
    simp only [Bool.false_eq_true, ↓reduceIte,
      MAU.Addition.HRS.borrowedIncrementOutput, target, Nat.FixedWidth.wordIncrement]

private lemma low_target_outside (length : Nat) (fits : length < width) (index : Fin width)
    (low : index.val < width - length) (nonzero : index.val ≠ 0) :
    (targetBit index).wire ∉ Set.range (evenSuffixSubsystem length fits).wires := by
  rintro ⟨source, same⟩
  have location := congrArg Fin.val same
  have bounded := source.isLt
  change source.val < length + length + 1 at bounded
  change (if source.val < length then source.val
    else if source.val < length + length then width + (source.val - length)
    else width + width - 1) = width + (width - 1 - index.val) at location
  have within := index.isLt
  split_ifs at location <;> omega

/-- Low bits are retained; bit zero is the preserved selected control itself. -/
lemma evenSuffix_low (length : Nat) (fits : length < width) (state : Registers) :
    (evenSuffixStep length fits state).1.2.val % 2 ^ (width - length) =
      state.1.2.val % 2 ^ (width - length) := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases low : index < width - length
  · by_cases zero : index = 0
    · subst index
      have read := evenSuffix_control length fits state
      simpa only [low, decide_true, Bool.true_and, targetLow, targetBit,
        MAU.Addition.TTK.ttkWithOverflowBit_get, MAU.Addition.TTK.ttkRightBit_get] using read
    · let selected : Fin width := ⟨index, by omega⟩
      have read := (evenSuffixSubsystem length fits).full_step_other_read
        (ModularAddition.source_onto length) encoding_onto (targetBit selected)
        (low_target_outside length fits selected low zero)
        MAU.Addition.HRS.controlledBorrowedIncrementOutput state
      simpa only [low, decide_true, Bool.true_and, evenSuffixStep, targetBit,
        MAU.Addition.TTK.ttkWithOverflowBit_get, MAU.Addition.TTK.ttkRightBit_get,
        selected] using read
  · simp only [low, decide_false, Bool.false_and]

/-- The original low target bit selects this complete unsigned high-word increment. -/
lemma evenSuffix_target_of_control (length : Nat) (fits : length < width)
    (state : Registers) (selected : targetLow.get state = true) :
    (evenSuffixStep length fits state).1.2.val =
      (state.1.2.val + 2 ^ (width - length)) % 2 ^ width := by
  have high := congrArg Fin.val (evenSuffix_high length fits state)
  rw [if_pos selected, Nat.FixedWidth.wordIncrement_val] at high
  have result := Nat.FixedWidth.ModularSuffix.increment_of_low_high
    (Nat.two_pow_pos (width - length)) (evenSuffix_low length fits state) high
  have widths : width - length + length = width := by omega
  rw [← Nat.pow_add, widths] at result
  exact result

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
