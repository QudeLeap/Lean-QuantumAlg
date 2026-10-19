/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.RegisterFrame
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

/-!
# Actual Work2 coordinates for the little-endian output coefficient

At divisor zero the recovered Work2 contains the coefficient in its
physical little-endian order [LYL+26, sec_EEA/sub_regshare.tex:20,263-264;
LYL+26, sec_EEA/sub_4phase.tex:123-125]. The ordinary native arithmetic
word is big-endian in physical wire order. This full-frame placement
reverses exactly those addresses and the same logical field coordinates.
All other words, finite lengths, and controls keep their original values.

The coordinate reversal is not an executed gate. The supplied real
arithmetic body is placed on these individual physical wires and retains
every native occurrence, with no additional workspace or omitted history.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.OutputOrientation

noncomputable section

/-- Invertible field grouping changes only the numerical reading direction of Work2. -/
def grouping (width : Nat) : Registers width ≃ Registers width where
  toFun state := { state with secondWord := state.secondWord.reverse }
  invFun state := { state with secondWord := state.secondWord.reverse }
  left_inv state := by
    cases state
    simp only [BitVec.reverse_reverse_eq]
  right_inv state := by
    cases state
    simp only [BitVec.reverse_reverse_eq]

/-- The same actual basis labels, with their complete explicit field encoding on both sides. -/
def indexEquiv (width : Nat) :
    (Qubits (encoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  (PreparedFrame.registerLabelEquiv width).symm.trans
    ((grouping width).symm.trans (PreparedFrame.registerLabelEquiv width))

lemma indexEquiv_encode (width : Nat) (state : Registers width) :
    indexEquiv width ((encoding width).encode (grouping width state)) =
      (encoding width).encode state := by
  change PreparedFrame.registerLabelEquiv width ((grouping width).symm
    ((PreparedFrame.registerLabelEquiv width).symm
      (PreparedFrame.registerLabelEquiv width (grouping width state)))) =
    PreparedFrame.registerLabelEquiv width state
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Only the contiguous original Work2 interval is reversed in the actual native addresses. -/
def physicalIndex (width index : Nat) : Nat :=
  if width + 3 ≤ index ∧ index < 2 * (width + 3) then
    3 * (width + 3) - 1 - index
  else index

/-- Work1 and every retained field after Work2 retain their actual physical coordinates. -/
lemma physicalIndex_outside (width index : Nat)
    (outside : index < width + 3 ∨ 2 * (width + 3) ≤ index) :
    physicalIndex width index = index := by
  have excluded : ¬(width + 3 ≤ index ∧ index < 2 * (width + 3)) := by omega
  exact if_neg excluded

/-- Each arithmetic Work2 address is placed at precisely its reversed original wire. -/
lemma physicalIndex_word (width : Nat) (index : Fin (width + 3)) :
    physicalIndex width (secondWordBit width index).wire.val =
      (secondWordBit width index.rev).wire.val := by
  rw [secondWordBit_wire, secondWordBit_wire]
  have within := index.isLt
  have selected : width + 3 ≤ width + 3 + index.val ∧
      width + 3 + index.val < 2 * (width + 3) := by omega
  unfold physicalIndex
  rw [if_pos selected, Fin.val_rev]
  omega

/-- The same logical Work2 bit reads the reversed original physical wire. -/
lemma grouping_word_bit (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    (secondWordBit width index).get (grouping width state) =
      (secondWordBit width index.rev).get state := by
  rw [secondWordBit_get, secondWordBit_get]
  change state.secondWord.reverse.getMsbD index.val = state.secondWord.getMsbD index.rev.val
  rw [BitVec.getMsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  have position : width + 3 - 1 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have within := index.isLt
    omega
  simp only [index.rev.isLt, decide_true, Bool.true_and, position]

/-- Every complete complementary field retains its exact input value under the grouping. -/
lemma grouping_retained (width : Nat) (state : Registers width) :
    (grouping width state).firstWord = state.firstWord ∧
      (grouping width state).coefficientLength = state.coefficientLength ∧
      (grouping width state).quotientLength = state.quotientLength ∧
      (grouping width state).divisorLength = state.divisorLength ∧
      (grouping width state).shift = state.shift ∧
      (grouping width state).flags = state.flags ∧
      (grouping width state).control = state.control := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma physicalIndex_injective (width : Nat) :
    Function.Injective
      (fun index : Fin (encoding width).width => physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  unfold physicalIndex at same
  dsimp only at same
  split at same <;> split at same <;> omega

private lemma physicalIndex_within (width : Nat) (index : Fin (encoding width).width) :
    physicalIndex width index.val < (encoding width).width := by
  have bound := index.isLt
  have complete := encoding_width width
  unfold physicalIndex
  split <;> omega

private def wireMap (width : Nat) :
    Fin (encoding width).width → Fin (encoding width).width := fun index =>
  ⟨physicalIndex width index.val, physicalIndex_within width index⟩

private lemma wireMap_injective (width : Nat) : Function.Injective (wireMap width) := by
  intro left right same
  exact physicalIndex_injective width (congrArg Fin.val same)

/-- The Work2 reversal and all fixed wires form one physical bijection. -/
def wireEquiv (width : Nat) :
    Fin (encoding width).width ≃ Fin (encoding width).width :=
  Equiv.ofBijective (wireMap width)
    ⟨wireMap_injective width, Finite.surjective_of_injective (wireMap_injective width)⟩

/-- The placement derives its semantic basis map from exactly the physical wire bijection. -/
def placement (width : Nat) : EncodedBit.FullPlacement (encoding width) (encoding width) :=
  EncodedBit.FullPlacement.ofWires (encoding width) (encoding width)
    (encoding_surjective width) (encoding_surjective width) (wireEquiv width)

private lemma placement_bit (width : Nat) (state : Registers width)
    (index : Fin (encoding width).width) :
    ((encoding width).encode ((placement width).grouping state)).val.testBit index.rev.val =
      ((encoding width).encode state).val.testBit (wireEquiv width index).rev.val := by
  have actual := EncodedBit.FullPlacement.wireBasis_bit
    (encoding width) (encoding width) (wireEquiv width)
    ((encoding width).encode ((placement width).grouping state)) index
  have encoded := (placement width).basis_encode state
  change EncodedBit.FullPlacement.wireBasis _ _ (wireEquiv width)
    ((encoding width).encode ((placement width).grouping state)) = _ at encoded
  rw [encoded] at actual
  exact actual.symm

private lemma bit_read (width : Nat) (bit : EncodedBit (encoding width))
    (state : Registers width) :
    bit.get state = ((encoding width).encode state).val.testBit bit.wire.rev.val := by
  rw [← bit.get_eq]
  apply congrArg (fun position => ((encoding width).encode state).val.testBit position)
  dsimp only [WireAddress.bitIndex, Fin.rev]
  omega

private lemma placed_read (width : Nat) (state : Registers width)
    (source target : EncodedBit (encoding width))
    (same : wireEquiv width source.wire = target.wire) :
    source.get ((placement width).grouping state) = target.get state := by
  rw [bit_read, bit_read]
  exact (placement_bit width state source.wire).trans
    (congrArg (fun wire : Fin (encoding width).width =>
      ((encoding width).encode state).val.testBit wire.rev.val) same)

private lemma retained_read (width : Nat) (state : Registers width)
    (bit : EncodedBit (encoding width))
    (outside : bit.wire.val < width + 3 ∨ 2 * (width + 3) ≤ bit.wire.val) :
    bit.get ((placement width).grouping state) = bit.get state := by
  apply placed_read width state bit bit
  apply Fin.ext
  change physicalIndex width bit.wire.val = bit.wire.val
  exact physicalIndex_outside width bit.wire.val outside

/-- The field grouping induced by the physical wire permutation is exactly Work2 reversal. -/
lemma placement_grouping (width : Nat) (state : Registers width) :
    (placement width).grouping state = grouping width state := by
  apply Registers.ext_fields
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (width + 3) := ⟨index, within⟩
    have actual := retained_read width state (firstWordBit width selected)
      (Or.inl (by rw [firstWordBit_wire]; exact selected.isLt))
    rw [firstWordBit_get, firstWordBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (width + 3) := ⟨index, within⟩
    have same : wireEquiv width (secondWordBit width selected).wire =
        (secondWordBit width selected.rev).wire := by
      apply Fin.ext
      change physicalIndex width (secondWordBit width selected).wire.val =
        (secondWordBit width selected.rev).wire.val
      exact physicalIndex_word width selected
    have actual := placed_read width state
      (secondWordBit width selected) (secondWordBit width selected.rev) same
    have expected := grouping_word_bit width selected state
    rw [secondWordBit_get, secondWordBit_get] at actual
    rw [secondWordBit_get, secondWordBit_get] at expected
    exact actual.trans expected.symm
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := retained_read width state (coefficientLengthBit width selected)
      (Or.inr (by rw [coefficientLengthBit_wire]; omega))
    rw [coefficientLengthBit_get, coefficientLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := retained_read width state (quotientLengthBit width selected)
      (Or.inr (by rw [quotientLengthBit_wire]; omega))
    rw [quotientLengthBit_get, quotientLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := retained_read width state (divisorLengthBit width selected)
      (Or.inr (by rw [divisorLengthBit_wire]; omega))
    rw [divisorLengthBit_get, divisorLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := retained_read width state (shiftBit width selected)
      (Or.inr (by rw [shiftBit_wire]; omega))
    rw [shiftBit_get, shiftBit_get] at actual
    exact actual
  · have actual := retained_read width state (phase1Bit width)
      (Or.inr (by rw [phase1Bit_wire]; omega))
    rw [phase1Bit_get, phase1Bit_get] at actual
    exact actual
  · have actual := retained_read width state (phase2Bit width)
      (Or.inr (by rw [phase2Bit_wire]; omega))
    rw [phase2Bit_get, phase2Bit_get] at actual
    exact actual
  · have actual := retained_read width state (signBit width)
      (Or.inr (by rw [signBit_wire]; omega))
    rw [signBit_get, signBit_get] at actual
    exact actual
  · have actual := retained_read width state (iterationBit width)
      (Or.inr (by rw [iterationBit_wire]; omega))
    rw [iterationBit_get, iterationBit_get] at actual
    exact actual
  · have actual := retained_read width state (controlBit width)
      (Or.inr (by rw [controlBit_wire]; omega))
    rw [controlBit_get, controlBit_get] at actual
    exact actual

/-- The full physical placement has the same exact source-level regrouping equivalence. -/
lemma placement_grouping_eq (width : Nat) :
    (placement width).grouping = grouping width := by
  apply Equiv.ext
  exact placement_grouping width

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputOrientation
