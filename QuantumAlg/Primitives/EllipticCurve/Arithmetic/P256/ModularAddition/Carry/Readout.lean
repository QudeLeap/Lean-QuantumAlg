/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Carry
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Exact P-256 complement-carry readout on the original two words

The HRS subsystem reads the original quantum target and toggles the original
flag exactly when that target is at least the field modulus. Every other
physical coordinate, including all borrowed addend bits, is restored.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit

private lemma pair_selected {Source Rest Target : Type} (grouping : Target ≃ Source × Rest)
    (test : Source → Bool) (update : Source → Source) (state : Target) :
    grouping.symm
        ((if test (grouping state).1 then update (grouping state).1 else (grouping state).1),
          (grouping state).2) =
      if test (grouping state).1 then
        grouping.symm (update (grouping state).1, (grouping state).2) else state := by
  by_cases selected : test (grouping state).1 = true
  · rw [if_pos selected, if_pos selected]
  · rw [if_neg selected, if_neg selected]
    exact grouping.symm_apply_apply state

private lemma full_pair_selected {Source Rest Target : Type}
    {source : BinaryLabelEncoding (Source × Rest)} {target : BinaryLabelEncoding Target}
    (placement : FullPlacement source target) (test : Source → Bool) (update : Source → Source)
    (state : Target) :
    placement.step (fun pair =>
      ((if test pair.1 then update pair.1 else pair.1), pair.2)) state =
      if test (placement.grouping state).1 then
        placement.step (fun pair => (update pair.1, pair.2)) state else state := by
  unfold FullPlacement.step
  exact pair_selected placement.grouping test update state

private lemma input_wire (index : Fin width) :
    carrySubsystem.wires (MAU.Addition.HRS.carryInputBit width index).wire =
      (targetBit index).wire := by
  apply Fin.ext
  change (if width - 1 - index.val < width then width + (width - 1 - index.val)
    else if width - 1 - index.val = width then width + width
    else width - 1 - index.val - width - 1) = width + (width - 1 - index.val)
  have bounded := index.isLt
  rw [if_pos (by simp only [width] at bounded ⊢; omega)]

private lemma output_wire :
    carrySubsystem.wires (MAU.Addition.HRS.carryOutputBit width).wire =
      reductionBit.wire := by
  apply Fin.ext
  rfl

/-- The complete physical grouping reads the actual target word, with no basis restriction. -/
lemma complementCarry_grouped_input (state : Registers) :
    ((carrySubsystem.full carryEncoding_onto encoding_onto).grouping state).1.1 =
      state.1.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have read := carrySubsystem.full_source_read carryEncoding_onto encoding_onto
    (MAU.Addition.HRS.carryInputBit width index) (targetBit index) (input_wire index) state
  simpa only [MAU.Addition.HRS.hrsCarryInputBit_get, targetBit,
    MAU.Addition.TTK.ttkWithOverflowBit_get, MAU.Addition.TTK.ttkRightBit_get] using read

private lemma output_flip (state : Registers) :
    (carrySubsystem.full carryEncoding_onto encoding_onto).step
      (fun pair => ((MAU.Addition.HRS.carryOutputBit width).flip pair.1, pair.2)) state =
        reductionBit.flip state := by
  have same : carrySubsystem.placeBit carryEncoding_onto encoding_onto
      (MAU.Addition.HRS.carryOutputBit width) = reductionBit :=
    EncodedBit.eq_of_wire_eq _ _
      ((carrySubsystem.placeBit_wire carryEncoding_onto encoding_onto _).trans output_wire)
  exact congrArg (fun bit : EncodedBit encoding => bit.flip state) same

/-- Carry by the actual sparse complement is exactly a modulus-comparison XOR. -/
lemma complementCarry_step_eq (state : Registers) :
    complementCarryStep state =
      if modulus ≤ state.1.2.val then reductionBit.flip state else state := by
  have grouped := complementCarry_grouped_input state
  have comparison :
      capacity ≤
          ((carrySubsystem.full carryEncoding_onto encoding_onto).grouping state).1.1.val +
            complement ↔ modulus ≤ state.1.2.val := by
    rw [grouped]
    have exactCapacity := modulus_add_complement
    omega
  have transported := full_pair_selected
    (carrySubsystem.full carryEncoding_onto encoding_onto)
    (fun original : MAU.Addition.HRS.CarryRegisters width =>
      decide (2 ^ width ≤ original.1.val + complementWord.val))
    (MAU.Addition.HRS.carryOutputBit width).flip state
  have source : complementCarryStep state =
      if decide (capacity ≤
          ((carrySubsystem.full carryEncoding_onto encoding_onto).grouping state).1.1.val +
            complement) then
        (carrySubsystem.full carryEncoding_onto encoding_onto).step
          (fun pair => ((MAU.Addition.HRS.carryOutputBit width).flip pair.1, pair.2)) state
      else state := by
    dsimp only [complementCarryStep, MAU.Addition.HRS.carryOutput]
    exact transported
  rw [source]
  by_cases selected : modulus ≤ state.1.2.val
  · rw [if_pos (decide_eq_true (comparison.mpr selected)), if_pos selected]
    exact output_flip state
  · rw [if_neg (by simpa only [decide_eq_true_eq] using (not_congr comparison).mpr selected),
      if_neg selected]

/-- The placed literal instructions have the same exact comparison action. -/
lemma complementCarryGates_step_eq (state : Registers) :
    EncodedBit.GateSpec.stepList complementCarryGates state =
      if modulus ≤ state.1.2.val then reductionBit.flip state else state := by
  rw [complementCarryGates_step, complementCarry_step_eq]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
