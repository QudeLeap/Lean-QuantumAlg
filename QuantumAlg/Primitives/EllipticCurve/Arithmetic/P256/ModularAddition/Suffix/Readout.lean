/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Suffix

/-!
# Original physical readouts of a controlled high-subword increment

The selected subsystem reads the actual high target bits and the original
reduction flag. Its native action restores the borrowed addend and every
unselected bit. No quantum operand becomes a classical program parameter.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

/-- The high subword of an actual unsigned operand. -/
def highWord (length : Nat) (fits : length ≤ width) (value : Fin (2 ^ width)) :
    Fin (2 ^ length) :=
  ⟨value.val / 2 ^ (width - length), by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    have widths : length + (width - length) = width := by omega
    rw [← Nat.pow_add, widths]
    exact value.isLt⟩

private def highIndex (length : Nat) (fits : length ≤ width) (index : Fin length) :
    Fin width :=
  ⟨width - length + index.val, by have bounded := index.isLt; omega⟩

private lemma target_wire (length : Nat) (fits : length ≤ width) (index : Fin length) :
    (suffixSubsystem length fits).wires
        (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.rightBit length index)).wire =
      (targetBit (highIndex length fits index)).wire := by
  apply Fin.ext
  change (if length + (length - 1 - index.val) < length then _
    else if length + (length - 1 - index.val) < length + length then _ else _) = _
  have bounded := index.isLt
  rw [if_neg (by omega), if_pos (by omega)]
  change width + (length + (length - 1 - index.val) - length) =
    width + (width - 1 - (width - length + index.val))
  omega

private lemma control_wire (length : Nat) (fits : length ≤ width) :
    (suffixSubsystem length fits).wires (MAU.Addition.TTK.overflowBit length).wire =
      reductionBit.wire := by
  apply Fin.ext
  change (if length + length < length then _
    else if length + length < length + length then _ else _) = width + width
  rw [if_neg (by omega), if_neg (by omega)]

/-- Grouping reads the actual high target word, including all input values. -/
lemma suffix_grouped_target (length : Nat) (fits : length ≤ width) (state : Registers) :
    (((suffixSubsystem length fits).full (source_onto length) encoding_onto).grouping
      state).1.1.2 = highWord length fits state.1.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have read := (suffixSubsystem length fits).full_source_read (source_onto length)
    encoding_onto
    (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.rightBit length index))
    (targetBit (highIndex length fits index)) (target_wire length fits index) state
  simpa only [MAU.Addition.TTK.ttkWithOverflowBit_get,
    MAU.Addition.TTK.ttkRightBit_get, targetBit, highIndex, highWord,
    Nat.testBit_div_two_pow, Nat.add_comm] using read

/-- The selected control is the original physical reduction flag. -/
lemma suffix_grouped_control (length : Nat) (fits : length ≤ width) (state : Registers) :
    (((suffixSubsystem length fits).full (source_onto length) encoding_onto).grouping
      state).1.2 = state.2 := by
  exact (suffixSubsystem length fits).full_source_read (source_onto length) encoding_onto
    (MAU.Addition.TTK.overflowBit length) reductionBit (control_wire length fits) state

/-- The actual controlled increment retains its original reduction flag. -/
lemma suffixIncrement_control (length : Nat) (fits : length ≤ width) (state : Registers) :
    (suffixIncrementStep length fits state).2 = state.2 := by
  have after := (suffixSubsystem length fits).full_step_source_read (source_onto length)
    encoding_onto (MAU.Addition.TTK.overflowBit length) reductionBit
    (control_wire length fits) MAU.Addition.HRS.controlledBorrowedIncrementOutput state
  have before := suffix_grouped_control length fits state
  change (suffixIncrementStep length fits state).2 =
    (MAU.Addition.HRS.controlledBorrowedIncrementOutput _).2 at after
  have restored : ∀ original : MAU.Addition.TTK.OverflowRegisters length,
      (MAU.Addition.HRS.controlledBorrowedIncrementOutput original).2 = original.2 := by
    intro original
    dsimp only [MAU.Addition.HRS.controlledBorrowedIncrementOutput]
    split <;> rfl
  exact after.trans ((restored _).trans before)

/-- High-word readout of the actual native action, with the original control retained. -/
lemma suffixIncrement_high (length : Nat) (fits : length ≤ width) (state : Registers) :
    highWord length fits (suffixIncrementStep length fits state).1.2 =
      if state.2 then Nat.FixedWidth.wordIncrement length (highWord length fits state.1.2)
      else highWord length fits state.1.2 := by
  let grouped := ((suffixSubsystem length fits).full (source_onto length)
    encoding_onto).grouping state
  have after := suffix_grouped_target length fits (suffixIncrementStep length fits state)
  have action :
      (((suffixSubsystem length fits).full (source_onto length) encoding_onto).grouping
        (suffixIncrementStep length fits state)).1 =
          MAU.Addition.HRS.controlledBorrowedIncrementOutput grouped.1 := by
    simp only [suffixIncrementStep, FullPlacement.step, Equiv.apply_symm_apply, grouped]
  rw [← after, action]
  have control := suffix_grouped_control length fits state
  have target := suffix_grouped_target length fits state
  change grouped.1.2 = state.2 at control
  change grouped.1.1.2 = highWord length fits state.1.2 at target
  dsimp only [MAU.Addition.HRS.controlledBorrowedIncrementOutput]
  rw [control]
  cases selected : state.2 <;>
    simp only [Bool.false_eq_true, ↓reduceIte,
      MAU.Addition.HRS.borrowedIncrementOutput, target, Nat.FixedWidth.wordIncrement]

private lemma low_target_outside (length : Nat) (fits : length ≤ width) (index : Fin width)
    (low : index.val < width - length) :
    (targetBit index).wire ∉ Set.range (suffixSubsystem length fits).wires := by
  rintro ⟨source, same⟩
  have location := congrArg Fin.val same
  have bounded := source.isLt
  change source.val < length + length + 1 at bounded
  change (if source.val < length then source.val
    else if source.val < length + length then width + (source.val - length)
    else width + width) = width + (width - 1 - index.val) at location
  have within := index.isLt
  split_ifs at location <;> omega

/-- All original low bits remain unchanged, including when the quantum control is true. -/
lemma suffixIncrement_low (length : Nat) (fits : length ≤ width) (state : Registers) :
    (suffixIncrementStep length fits state).1.2.val % 2 ^ (width - length) =
      state.1.2.val % 2 ^ (width - length) := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases low : index < width - length
  · let selected : Fin width := ⟨index, by omega⟩
    have read := (suffixSubsystem length fits).full_step_other_read (source_onto length)
      encoding_onto (targetBit selected) (low_target_outside length fits selected low)
      MAU.Addition.HRS.controlledBorrowedIncrementOutput state
    simpa only [low, decide_true, Bool.true_and, suffixIncrementStep, targetBit,
      MAU.Addition.TTK.ttkWithOverflowBit_get, MAU.Addition.TTK.ttkRightBit_get,
      selected] using read
  · simp only [low, decide_false, Bool.false_and]

/-- A true original control adds the actual suffix place value modulo the full word. -/
lemma suffixIncrement_target_of_control (length : Nat) (fits : length ≤ width)
    (state : Registers) (selected : state.2 = true) :
    (suffixIncrementStep length fits state).1.2.val =
      (state.1.2.val + 2 ^ (width - length)) % 2 ^ width := by
  have high := congrArg Fin.val (suffixIncrement_high length fits state)
  rw [if_pos selected, Nat.FixedWidth.wordIncrement_val] at high
  have result := Nat.FixedWidth.ModularSuffix.increment_of_low_high
    (Nat.two_pow_pos (width - length)) (suffixIncrement_low length fits state) high
  have widths : width - length + length = width := by omega
  rw [← Nat.pow_add, widths] at result
  exact result

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
