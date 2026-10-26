/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix

/-! # Complete borrowed-word restoration and unsigned action of the actual suffix program -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

private lemma borrowed_wire (length : Nat) (fits : length ≤ width) (index : Fin length) :
    (suffixSubsystem length fits).wires
        (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.leftBit length index)).wire =
      (addendBit (highIndex length fits index)).wire := by
  apply Fin.ext
  change (if length - 1 - index.val < length then _
    else if length - 1 - index.val < length + length then _ else _) = _
  have bounded := index.isLt
  rw [if_pos (by omega)]
  change length - 1 - index.val = width - 1 - (width - length + index.val)
  omega

private lemma low_addend_outside (length : Nat) (fits : length ≤ width) (index : Fin width)
    (low : index.val < width - length) :
    (addendBit index).wire ∉ Set.range (suffixSubsystem length fits).wires := by
  rintro ⟨source, same⟩
  have location := congrArg Fin.val same
  have bounded := source.isLt
  change source.val < length + length + 1 at bounded
  change (if source.val < length then source.val
    else if source.val < length + length then width + (source.val - length)
    else width + width) = width - 1 - index.val at location
  have within := index.isLt
  split_ifs at location <;> omega

/-- Every actual addend bit is retained, including the borrowed high subword. -/
lemma suffixIncrement_addend (length : Nat) (fits : length ≤ width) (state : Registers) :
    (suffixIncrementStep length fits state).1.1 = state.1.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  by_cases low : index.val < width - length
  · have read := (suffixSubsystem length fits).full_step_other_read (source_onto length)
      encoding_onto (addendBit index) (low_addend_outside length fits index low)
      MAU.Addition.HRS.controlledBorrowedIncrementOutput state
    simpa only [suffixIncrementStep, addendBit, MAU.Addition.TTK.ttkWithOverflowBit_get,
      MAU.Addition.TTK.ttkLeftBit_get] using read
  · let selected : Fin length := ⟨index.val - (width - length), by
      have within := index.isLt
      omega⟩
    have same : highIndex length fits selected = index := by
      apply Fin.ext
      dsimp only [highIndex, selected]
      omega
    have before := (suffixSubsystem length fits).full_source_read (source_onto length)
      encoding_onto
      (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.leftBit length selected))
      (addendBit (highIndex length fits selected)) (borrowed_wire length fits selected) state
    have after := (suffixSubsystem length fits).full_step_source_read (source_onto length)
      encoding_onto
      (MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.leftBit length selected))
      (addendBit (highIndex length fits selected)) (borrowed_wire length fits selected)
      MAU.Addition.HRS.controlledBorrowedIncrementOutput state
    have restored : ∀ original : MAU.Addition.TTK.OverflowRegisters length,
        (MAU.Addition.HRS.controlledBorrowedIncrementOutput original).1.1 = original.1.1 := by
      intro original
      have actual := MAU.Addition.HRS.hrsControlledBorrowedIncrement_restores length original
      rw [MAU.Addition.HRS.hrsControlledBorrowedIncrement_step] at actual
      exact actual.1
    simp only [same, MAU.Addition.TTK.ttkWithOverflowBit_get,
      MAU.Addition.TTK.ttkLeftBit_get, restored] at before after
    simpa only [suffixIncrementStep, addendBit, MAU.Addition.TTK.ttkWithOverflowBit_get,
      MAU.Addition.TTK.ttkLeftBit_get] using after.trans before

/-- A false original flag makes the entire actual physical action the identity. -/
lemma suffixIncrement_of_control_false (length : Nat) (fits : length ≤ width)
    (state : Registers) (disabled : state.2 = false) :
    suffixIncrementStep length fits state = state := by
  let placement := (suffixSubsystem length fits).full (source_onto length) encoding_onto
  have control : (placement.grouping state).1.2 = false :=
    (suffix_grouped_control length fits state).trans disabled
  have fixed : MAU.Addition.HRS.controlledBorrowedIncrementOutput
      (placement.grouping state).1 = (placement.grouping state).1 := by
    dsimp only [MAU.Addition.HRS.controlledBorrowedIncrementOutput]
    rw [control]
    rfl
  change placement.grouping.symm
    (MAU.Addition.HRS.controlledBorrowedIncrementOutput (placement.grouping state).1,
      (placement.grouping state).2) = state
  rw [fixed]
  exact placement.grouping.symm_apply_apply state

/-- The complete original frame translates only its target word under the original flag. -/
def suffixWordStep (length : Nat) (state : Registers) : Registers :=
  if state.2 then
    ((state.1.1, ⟨(state.1.2.val + 2 ^ (width - length)) % 2 ^ width,
      Nat.mod_lt _ (Nat.two_pow_pos width)⟩), state.2)
  else state

/-- Full native semantics, including the complete arbitrary borrowed word and flag. -/
lemma suffixIncrementStep_eq_wordStep (length : Nat) (fits : length ≤ width)
    (state : Registers) :
    suffixIncrementStep length fits state = suffixWordStep length state := by
  by_cases selected : state.2 = true
  · rw [suffixWordStep, if_pos selected]
    apply Prod.ext
    · apply Prod.ext
      · exact suffixIncrement_addend length fits state
      · apply Fin.ext
        exact suffixIncrement_target_of_control length fits state selected
    · exact suffixIncrement_control length fits state
  · have disabled : state.2 = false := Bool.eq_false_iff.mpr selected
    rw [suffixWordStep, if_neg selected]
    exact suffixIncrement_of_control_false length fits state disabled

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
