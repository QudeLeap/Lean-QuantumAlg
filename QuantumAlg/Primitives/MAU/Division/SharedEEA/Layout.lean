/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

/-!
# Division accumulation on the corrected shared-EEA coefficient

The native source port reads the first n Work2 wires in reverse physical
order, hence the numerical word `secondWord.reverse.setWidth n`. The numerator
and target are separate arbitrary words. Work1, the remaining Work2 bits, and all
length/control fields form the complete retained history. Both the basis
transport and physical placement follow the same explicit wire bijection.
-/

namespace QuantumAlg.MAU.Division.SharedEEA

noncomputable section

open BinaryLabelEncoding
open Inversion.SharedEEA

/-- The entire shared-EEA frame followed by independent numerator and target words. -/
abbrev Frame (width : Nat) :=
  Inversion.SharedEEA.Registers width × (Fin (2 ^ width) × Fin (2 ^ width))

/-- Original Work1, three remaining Work2 bits, and every original small field. -/
def historyWidth (width : Nat) : Nat := Accumulate.historyWidth width

/-- The existing physical frame, numerator, and target retain their original order. -/
def frameEncoding (width : Nat) : BinaryLabelEncoding (Frame width) :=
  BinaryLabelEncoding.prod (Inversion.SharedEEA.encoding width)
    (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))

/-- The native product accumulator's three words and every unselected original bit. -/
def sourceEncoding (width : Nat) :
    BinaryLabelEncoding
      (Multiplication.VariableGidney.Registers width × Fin (2 ^ historyWidth width)) :=
  BinaryLabelEncoding.prod (Multiplication.VariableGidney.encoding width)
    (finIdentity (historyWidth width))

lemma divisionFrame_width (width : Nat) :
    (frameEncoding width).width = 4 * width + 11 + 4 * width.size := by
  change (Inversion.SharedEEA.encoding width).width + (width + width) = _
  rw [Inversion.SharedEEA.encoding_width]
  omega

private lemma source_width (width : Nat) :
    (sourceEncoding width).width = 4 * width + 11 + 4 * width.size := by
  change (width + (width + width)) + historyWidth width = _
  unfold historyWidth Accumulate.historyWidth
  omega

/-- Group inverse, numerator, target, and all untouched EEA history at actual addresses. -/
def address (width index : Nat) : Nat :=
  if index < width then 2 * width + 2 - index
  else if index < 3 * width then width + 11 + 4 * width.size + index
  else if index < 4 * width + 3 then index - 3 * width
  else index - 2 * width

private def sourceAddress (width index : Nat) : Nat :=
  if index < width + 3 then 3 * width + index
  else if index < 2 * width + 3 then 2 * width + 2 - index
  else if index < 2 * width + 11 + 4 * width.size then index + 2 * width
  else index - (width + 11 + 4 * width.size)

private def wirePermutation (width : Nat) :
    Equiv.Perm (Fin (4 * width + 11 + 4 * width.size)) where
  toFun index := ⟨address width index.val, by
    have bound := index.isLt
    unfold address
    split_ifs <;> omega⟩
  invFun index := ⟨sourceAddress width index.val, by
    have bound := index.isLt
    unfold sourceAddress
    split_ifs <;> omega⟩
  left_inv index := by
    apply Fin.ext
    have bound := index.isLt
    change sourceAddress width (address width index.val) = index.val
    unfold sourceAddress address
    split_ifs <;> omega
  right_inv index := by
    apply Fin.ext
    have bound := index.isLt
    change address width (sourceAddress width index.val) = index.val
    unfold sourceAddress address
    split_ifs <;> omega

/-- Exact full wire bijection, including the width-zero case. -/
def wires (width : Nat) : Fin (sourceEncoding width).width ≃ Fin (frameEncoding width).width :=
  (finCongr (source_width width)).trans
    ((wirePermutation width).trans (finCongr (divisionFrame_width width).symm))

private lemma frame_total (width : Nat) :
    Function.Surjective (frameEncoding width).encode := by
  intro label
  obtain ⟨⟨shared, words⟩, rfl⟩ :=
    (prodEquiv (m := (Inversion.SharedEEA.encoding width).width)
      (n := width + width)).surjective label
  obtain ⟨state, rfl⟩ := Inversion.SharedEEA.encoding_surjective width shared
  obtain ⟨⟨numerator, target⟩, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective words
  exact ⟨(state, numerator, target), rfl⟩

private lemma source_total (width : Nat) :
    Function.Surjective (sourceEncoding width).encode := by
  intro label
  obtain ⟨⟨words, history⟩, rfl⟩ :=
    (prodEquiv (m := width + (width + width)) (n := historyWidth width)).surjective label
  obtain ⟨⟨inverse, rest⟩, rfl⟩ :=
    (prodEquiv (m := width) (n := width + width)).surjective words
  obtain ⟨⟨numerator, target⟩, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective rest
  exact ⟨((inverse, numerator, target), history), rfl⟩

/-- Semantic grouping and physical addresses are derived from the very same wires. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (sourceEncoding width) (frameEncoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (source_total width) (frame_total width) (wires width)

lemma divisionWires_address (width : Nat) (index : Fin (sourceEncoding width).width) :
    (wires width index).val = address width index.val := rfl

private lemma grouping_bit (width : Nat) (state : Frame width)
    (index : Fin (sourceEncoding width).width) :
    ((sourceEncoding width).encode ((placement width).grouping state)).val.testBit index.rev.val =
      ((frameEncoding width).encode state).val.testBit (wires width index).rev.val := by
  have actual := EncodedBit.FullPlacement.wireBasis_bit
    (sourceEncoding width) (frameEncoding width) (wires width)
    ((sourceEncoding width).encode ((placement width).grouping state)) index
  have encoded := (placement width).basis_encode state
  change EncodedBit.FullPlacement.wireBasis _ _ (wires width)
    ((sourceEncoding width).encode ((placement width).grouping state)) = _ at encoded
  rw [encoded] at actual
  exact actual.symm

private lemma bit_read {Data : Type} {label : BinaryLabelEncoding Data}
    (bit : EncodedBit label) (state : Data) :
    bit.get state = (label.encode state).val.testBit bit.wire.rev.val := by
  rw [← bit.get_eq]
  apply congrArg (fun position => (label.encode state).val.testBit position)
  dsimp only [WireAddress.bitIndex, Fin.rev]
  omega

private lemma placed_read (width : Nat) (state : Frame width)
    (source : EncodedBit (sourceEncoding width)) (target : EncodedBit (frameEncoding width))
    (same : wires width source.wire = target.wire) :
    source.get ((placement width).grouping state) = target.get state := by
  rw [bit_read, bit_read]
  exact (grouping_bit width state source.wire).trans
    (congrArg (fun wire : Fin (frameEncoding width).width =>
      ((frameEncoding width).encode state).val.testBit wire.rev.val) same)

private def sourceBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (Multiplication.VariableGidney.encoding width) (finIdentity (historyWidth width))
    (prodLeftBit (finIdentity width)
      (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))
      (finIdentityBit width index))

private def numeratorBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (Multiplication.VariableGidney.encoding width) (finIdentity (historyWidth width))
    (prodRightBit (finIdentity width)
      (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))
      (prodLeftBit (finIdentity width) (finIdentity width) (finIdentityBit width index)))

private def targetBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (Multiplication.VariableGidney.encoding width) (finIdentity (historyWidth width))
    (prodRightBit (finIdentity width)
      (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))
      (prodRightBit (finIdentity width) (finIdentity width) (finIdentityBit width index)))

/-- The placed native source is the corrected coefficient in its actual numerical orientation. -/
lemma divisionGrouping_source (width : Nat) (state : Frame width) :
    ((placement width).grouping state).1.1 = OutputCopy.value state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  let source := sourceBit width index.rev
  let target := prodLeftBit (Inversion.SharedEEA.encoding width)
    (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))
    (secondWordBit width ⟨index.val, by omega⟩)
  have same : wires width source.wire = target.wire := by
    apply Fin.ext
    rw [divisionWires_address]
    change address width index.rev.val = width + 3 + index.val
    unfold address
    rw [if_pos index.rev.isLt]
    have bound := index.isLt
    simp only [Fin.rev]
    omega
  have actual := placed_read width state source target same
  change (finIdentityBit width index.rev).get ((placement width).grouping state).1.1 =
    (secondWordBit width ⟨index.val, by omega⟩).get state.1 at actual
  rw [bit_read, secondWordBit_get] at actual
  change ((placement width).grouping state).1.1.val.testBit index.rev.rev.val = _ at actual
  rw [Fin.rev_rev] at actual
  change _ = (state.1.secondWord.reverse.setWidth width).getLsbD index.val
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  simpa only [index.isLt, decide_true, Bool.true_and] using actual

/-- The first external word remains the independent numerator, including zero and nonunits. -/
lemma divisionGrouping_numerator (width : Nat) (state : Frame width) :
    ((placement width).grouping state).1.2.1 = state.2.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  let source := numeratorBit width index.rev
  let target := prodRightBit (Inversion.SharedEEA.encoding width)
    (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))
    (prodLeftBit (finIdentity width) (finIdentity width) (finIdentityBit width index.rev))
  have same : wires width source.wire = target.wire := by
    apply Fin.ext
    rw [divisionWires_address]
    change address width (width + index.rev.val) =
      (Inversion.SharedEEA.encoding width).width + index.rev.val
    rw [Inversion.SharedEEA.encoding_width]
    unfold address
    have bound := index.rev.isLt
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have actual := placed_read width state source target same
  change (finIdentityBit width index.rev).get ((placement width).grouping state).1.2.1 =
    (finIdentityBit width index.rev).get state.2.1 at actual
  rw [bit_read, bit_read] at actual
  change ((placement width).grouping state).1.2.1.val.testBit index.rev.rev.val =
    state.2.1.val.testBit index.rev.rev.val at actual
  simpa only [Fin.rev_rev] using actual

/-- The placed native target is the caller's complete separate accumulator. -/
lemma divisionGrouping_target (width : Nat) (state : Frame width) :
    ((placement width).grouping state).1.2.2 = state.2.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  let source := targetBit width index.rev
  let target := prodRightBit (Inversion.SharedEEA.encoding width)
    (BinaryLabelEncoding.prod (finIdentity width) (finIdentity width))
    (prodRightBit (finIdentity width) (finIdentity width) (finIdentityBit width index.rev))
  have same : wires width source.wire = target.wire := by
    apply Fin.ext
    rw [divisionWires_address]
    change address width (width + (width + index.rev.val)) =
      (Inversion.SharedEEA.encoding width).width + (width + index.rev.val)
    rw [Inversion.SharedEEA.encoding_width]
    unfold address
    have bound := index.rev.isLt
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have actual := placed_read width state source target same
  change (finIdentityBit width index.rev).get ((placement width).grouping state).1.2.2 =
    (finIdentityBit width index.rev).get state.2.2 at actual
  rw [bit_read, bit_read] at actual
  change ((placement width).grouping state).1.2.2.val.testBit index.rev.rev.val =
    state.2.2.val.testBit index.rev.rev.val at actual
  simpa only [Fin.rev_rev] using actual

private lemma address_history_bound (width index : Nat) (bound : index < historyWidth width) :
    address width (3 * width + index) < 2 * width + 11 + 4 * width.size := by
  unfold historyWidth Accumulate.historyWidth at bound
  unfold address
  split_ifs <;> omega

/-- Changing only the separate target preserves the entire grouped history, on every frame. -/
lemma divisionGrouping_history (width : Nat) (frame : Inversion.SharedEEA.Registers width)
    (numerator left right : Fin (2 ^ width)) :
    ((placement width).grouping (frame, numerator, left)).2 =
      ((placement width).grouping (frame, numerator, right)).2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  let bit : EncodedBit (sourceEncoding width) :=
    prodRightBit (Multiplication.VariableGidney.encoding width)
      (finIdentity (historyWidth width)) (finIdentityBit (historyWidth width) index.rev)
  have wireBound : (wires width bit.wire).val < (Inversion.SharedEEA.encoding width).width := by
    rw [divisionWires_address, Inversion.SharedEEA.encoding_width]
    change address width ((width + (width + width)) + index.rev.val) < _
    have actual := address_history_bound width index.rev.val index.rev.isLt
    have position : width + (width + width) + index.rev.val = 3 * width + index.rev.val := by omega
    rw [position]
    omega
  let offset : Fin (Inversion.SharedEEA.encoding width).width :=
    ⟨(Inversion.SharedEEA.encoding width).width - 1 - (wires width bit.wire).val, by omega⟩
  have same (target : Fin (2 ^ width)) :
      ((frameEncoding width).encode (frame, numerator, target)).val.testBit
          (wires width bit.wire).rev.val =
        ((Inversion.SharedEEA.encoding width).encode frame).val.testBit offset.val := by
    have actual := prodEquiv_testBit_left
      (m := (Inversion.SharedEEA.encoding width).width) (n := width + width)
      ((Inversion.SharedEEA.encoding width).encode frame)
      (prodEquiv (numerator, target)) offset
    have position : (wires width bit.wire).rev.val = (width + width) + offset.val := by
      change (Inversion.SharedEEA.encoding width).width + (width + width) -
        ((wires width bit.wire).val + 1) = (width + width) +
          ((Inversion.SharedEEA.encoding width).width - 1 - (wires width bit.wire).val)
      omega
    rw [position]
    exact actual
  have read (target : Fin (2 ^ width)) :
      ((placement width).grouping (frame, numerator, target)).2.val.testBit index.val =
        ((Inversion.SharedEEA.encoding width).encode frame).val.testBit offset.val := by
    have source := bit_read bit ((placement width).grouping (frame, numerator, target))
    have actual := source.trans (grouping_bit width (frame, numerator, target) bit.wire)
    change (finIdentityBit (historyWidth width) index.rev).get
      ((placement width).grouping (frame, numerator, target)).2 = _ at actual
    have joined := actual.trans (same target)
    rw [bit_read] at joined
    change ((placement width).grouping (frame, numerator, target)).2.val.testBit
      index.rev.rev.val = _ at joined
    simpa only [Fin.rev_rev] using joined
  exact (read left).trans (read right).symm

end

end QuantumAlg.MAU.Division.SharedEEA
