/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

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

theorem indexEquiv_encode (width : Nat) (state : Registers width) :
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
theorem physicalIndex_outside (width index : Nat)
    (outside : index < width + 3 ∨ 2 * (width + 3) ≤ index) :
    physicalIndex width index = index := by
  have excluded : ¬(width + 3 ≤ index ∧ index < 2 * (width + 3)) := by omega
  exact if_neg excluded

/-- Each arithmetic Work2 address is placed at precisely its reversed original wire. -/
theorem physicalIndex_word (width : Nat) (index : Fin (width + 3)) :
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
theorem grouping_word_bit (width : Nat) (index : Fin (width + 3))
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
theorem grouping_retained (width : Nat) (state : Registers width) :
    (grouping width state).firstWord = state.firstWord ∧
      (grouping width state).coefficientLength = state.coefficientLength ∧
      (grouping width state).quotientLength = state.quotientLength ∧
      (grouping width state).divisorLength = state.divisorLength ∧
      (grouping width state).shift = state.shift ∧
      (grouping width state).flags = state.flags ∧
      (grouping width state).control = state.control := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem physicalIndex_injective (width : Nat) :
    Function.Injective
      (fun index : Fin (encoding width).width => physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  unfold physicalIndex at same
  dsimp only at same
  split at same <;> split at same <;> omega

private theorem physicalIndex_within (width : Nat) (index : Fin (encoding width).width) :
    physicalIndex width index.val < (encoding width).width := by
  have bound := index.isLt
  have complete := encoding_width width
  unfold physicalIndex
  split <;> omega

/-- The shared placement engine receives the proved basis map and these same native coordinates. -/
def placement (width : Nat) : EncodedBit.FullPlacement (encoding width) (encoding width) where
  grouping := grouping width
  basis := indexEquiv width
  basis_encode := indexEquiv_encode width
  physicalIndex := physicalIndex width
  wire_injective := physicalIndex_injective width
  wire_within := physicalIndex_within width

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputOrientation
