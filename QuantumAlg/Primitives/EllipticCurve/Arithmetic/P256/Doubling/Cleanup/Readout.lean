/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Cleanup.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Carry.Readout

/-! # Complete original-frame action of the actual doubling flag cleanup -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private def upperIndex (index : Fin highWidth) : Fin width :=
  ⟨index.val + 1, by
    have within := index.isLt
    change index.val < 255 at within
    change index.val + 1 < 256
    omega⟩

private lemma input_wire (index : Fin highWidth) :
    comparisonSubsystem.wires (MAU.Addition.HRS.carryInputBit highWidth index).wire =
      (targetBit (upperIndex index)).wire := by
  apply Fin.ext
  change (if highWidth - 1 - index.val < highWidth then
      width + (highWidth - 1 - index.val)
    else if highWidth - 1 - index.val = highWidth then width + width
    else highWidth - 1 - index.val - highWidth - 1) =
      width + (width - 1 - (index.val + 1))
  have within := index.isLt
  have widths : width = highWidth + 1 := rfl
  rw [if_pos (by omega)]
  omega

/-- The selected physical subsystem reads precisely the original target divided by two. -/
lemma doublingCleanup_grouped_input (state : Registers) :
    ((comparisonSubsystem.full high_onto encoding_onto).grouping state).1.1 =
      highWord highWidth (by decide) state.1.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have read := comparisonSubsystem.full_source_read high_onto encoding_onto
    (MAU.Addition.HRS.carryInputBit highWidth index) (targetBit (upperIndex index))
    (input_wire index) state
  have widths : width - highWidth = 1 := by decide
  simpa only [MAU.Addition.HRS.hrsCarryInputBit_get, targetBit,
    MAU.Addition.TTK.ttkWithOverflowBit_get, MAU.Addition.TTK.ttkRightBit_get,
    upperIndex, highWord, widths, Nat.testBit_div_two_pow, Nat.add_comm] using read

private lemma output_wire :
    comparisonSubsystem.wires (MAU.Addition.HRS.carryOutputBit highWidth).wire =
      reductionBit.wire := by
  apply Fin.ext
  change (if highWidth < highWidth then width + highWidth
    else if highWidth = highWidth then width + width else highWidth - highWidth - 1) =
      width + width
  rw [if_neg (Nat.lt_irrefl _), if_pos rfl]

private lemma output_flip (state : Registers) :
    (comparisonSubsystem.full high_onto encoding_onto).step
      (fun pair => ((MAU.Addition.HRS.carryOutputBit highWidth).flip pair.1, pair.2)) state =
        reductionBit.flip state := by
  have same : comparisonSubsystem.placeBit high_onto encoding_onto
      (MAU.Addition.HRS.carryOutputBit highWidth) = reductionBit :=
    EncodedBit.eq_of_wire_eq _ _
      ((comparisonSubsystem.placeBit_wire high_onto encoding_onto _).trans output_wire)
  exact congrArg (fun bit : EncodedBit encoding => bit.flip state) same

/-- The actual unselected comparison toggles only the original reduction flag. -/
lemma doublingCleanup_comparison_step (state : Registers) :
    comparisonStep state =
      if complement / 2 ≤ state.1.2.val / 2 then reductionBit.flip state else state := by
  have grouped := congrArg Fin.val (doublingCleanup_grouped_input state)
  have balance : complement / 2 + comparisonConstant.val = 2 ^ highWidth := by
    have bounded : complement / 2 ≤ 2 ^ highWidth := by norm_num [complement]
    exact Nat.add_sub_of_le bounded
  have comparison :
      2 ^ highWidth ≤
          ((comparisonSubsystem.full high_onto encoding_onto).grouping state).1.1.val +
            comparisonConstant.val ↔ complement / 2 ≤ state.1.2.val / 2 := by
    change _ = state.1.2.val / 2 at grouped
    rw [grouped]
    omega
  have transported := ModularAddition.full_pair_selected
    (comparisonSubsystem.full high_onto encoding_onto)
    (fun original : MAU.Addition.HRS.CarryRegisters highWidth =>
      decide (2 ^ highWidth ≤ original.1.val + comparisonConstant.val))
    (MAU.Addition.HRS.carryOutputBit highWidth).flip state
  have source : comparisonStep state =
      if decide (2 ^ highWidth ≤
          ((comparisonSubsystem.full high_onto encoding_onto).grouping state).1.1.val +
            comparisonConstant.val) then
        (comparisonSubsystem.full high_onto encoding_onto).step
          (fun pair => ((MAU.Addition.HRS.carryOutputBit highWidth).flip pair.1, pair.2)) state
      else state := by
    dsimp only [comparisonStep, MAU.Addition.HRS.carryOutput]
    exact transported
  rw [source]
  by_cases selected : complement / 2 ≤ state.1.2.val / 2
  · rw [if_pos (decide_eq_true (comparison.mpr selected)), if_pos selected]
    exact output_flip state
  · rw [if_neg (by simpa only [decide_eq_true_eq] using (not_congr comparison).mpr selected),
      if_neg selected]

private lemma reduction_flip_low (state : Registers) :
    targetLow.get (reductionBit.flip state) = targetLow.get state :=
  EncodedBit.get_flip_of_wire_ne reductionBit targetLow low_reduction_ne.symm state

private lemma cleanup_upper_step (state : Registers) :
    cleanupStep state =
      if targetLow.get state = true ∧ state.1.2.val / 2 < complement / 2 then
        reductionBit.flip state else state := by
  rw [cleanupStep, cleanupGates, stepList_append, selectedComparisonGates_step]
  by_cases selected : targetLow.get state = true
  · rw [if_pos selected, doublingCleanup_comparison_step]
    by_cases small : state.1.2.val / 2 < complement / 2
    · rw [if_neg (Nat.not_le.mpr small), if_pos ⟨selected, small⟩]
      change cnotStep targetLow reductionBit state = reductionBit.flip state
      rw [cnotStep, if_pos selected]
    · rw [if_pos (Nat.le_of_not_gt small), if_neg (by omega)]
      change cnotStep targetLow reductionBit (reductionBit.flip state) = state
      rw [cnotStep, reduction_flip_low, if_pos selected, EncodedBit.flip_flip]
  · rw [if_neg selected, if_neg (fun condition => selected condition.1)]
    change cnotStep targetLow reductionBit state = state
    rw [cnotStep, if_neg selected]

/-- Actual cleanup toggles precisely odd results below the sparse complement.
Every physical source bit and target bit is retained, with no work-clean premise. -/
lemma doublingCleanup_step_eq (state : Registers) :
    cleanupStep state =
      if targetLow.get state = true ∧ state.1.2.val < complement then
        reductionBit.flip state else state := by
  have upper := cleanup_upper_step state
  by_cases selected : targetLow.get state = true
  · have odd : state.1.2.val % 2 = 1 := by
      have bit : state.1.2.val.testBit 0 = true := selected
      have nonzero := Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true _ bit
      omega
    have comparison := Nat.FixedWidth.NearPower.odd_comparison_upper_bits complement_odd odd
    by_cases small : state.1.2.val < complement
    · rw [if_pos ⟨selected, comparison.mp small⟩] at upper
      rw [if_pos ⟨selected, small⟩]
      exact upper
    · rw [if_neg (fun condition => small (comparison.mpr condition.2))] at upper
      rw [if_neg (fun condition => small condition.2)]
      exact upper
  · rw [if_neg (fun condition => selected condition.1)] at upper
    rw [if_neg (fun condition => selected condition.1)]
    exact upper

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup
