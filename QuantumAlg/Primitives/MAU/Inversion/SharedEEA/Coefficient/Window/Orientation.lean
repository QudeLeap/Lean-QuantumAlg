/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Encoding

/-!
# Exact little-endian coefficient windows and retained complementary bits

The coefficient source is the leading Work1 field in physical
little-endian order. Its target is the aligned leading integer part of
Work2; the rotated fractional part remains outside the selected region
[LYL+26, sec_EEA/sub_regshare.tex:17,20,263-264,291-294].

Consequently its TTK grouping swaps the two remainder operand roles and
reverses their finite bit order. This is an exact invertible description
of the real wire labels, retaining every other original bit. It is not
an additional gate or an executed word reversal. The subsequent placement
maps the actual TTK elementary gates to these exact physical coordinates.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowOrientation

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowEncoding

/-- The actual coefficient region starts at the left edge and retains its entire suffix. -/
def coefficientWindow (width length : Nat) (fits : length ≤ width + 3) : Window width where
  above := 0
  length := length
  below := width + 3 - length
  complete := by omega

private def reverseWord (length : Nat) : BitVec length ≃ BitVec length where
  toFun word := word.reverse
  invFun word := word.reverse
  left_inv _ := BitVec.reverse_reverse_eq
  right_inv _ := BitVec.reverse_reverse_eq

/-- Reverse the actual finite operand bits, with an explicit inverse at every width. -/
def reverseValue (length : Nat) : Fin (2 ^ length) ≃ Fin (2 ^ length) :=
  BitVec.equivFin.toEquiv.symm.trans
    ((reverseWord length).trans BitVec.equivFin.toEquiv)

private theorem reverseValue_word {length : Nat} (word : BitVec length) :
    reverseValue length (BitVec.equivFin word) = BitVec.equivFin word.reverse := by
  change BitVec.equivFin
    (BitVec.equivFin.toEquiv.symm (BitVec.equivFin.toEquiv word)).reverse = _
  rw [Equiv.symm_apply_apply]

/-- Two actual bit reversals restore the complete finite operand. -/
theorem reverseValue_twice (length : Nat) (value : Fin (2 ^ length)) :
    reverseValue length (reverseValue length value) = value := by
  obtain ⟨word, rfl⟩ := BitVec.equivFin.toEquiv.surjective value
  change reverseValue length (reverseValue length (BitVec.equivFin word)) = BitVec.equivFin word
  rw [reverseValue_word, reverseValue_word, BitVec.reverse_reverse_eq]

/-- A reflected coefficient operand reads the opposite bit of the original finite word. -/
theorem reverseValue_testBit (length : Nat) (value : Fin (2 ^ length))
    (index : Fin length) :
    (reverseValue length value).val.testBit index.val =
      value.val.testBit index.rev.val := by
  obtain ⟨word, rfl⟩ := BitVec.equivFin.toEquiv.surjective value
  change (reverseValue length (BitVec.equivFin word)).val.testBit index.val =
    (BitVec.equivFin word).val.testBit index.rev.val
  rw [reverseValue_word]
  change word.reverse.getLsbD index.val = word.getLsbD index.rev.val
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  have position : length - 1 - index.val = index.rev.val := by
    rw [Fin.val_rev]
    have within := index.isLt
    omega
  simp only [index.isLt, decide_true, Bool.true_and, position]

/-- Swap source/target roles and read both actual windows in their coefficient bit order. -/
def focus (length : Nat) :
    Addition.TTK.OverflowRegisters length ≃ Addition.TTK.OverflowRegisters length where
  toFun pair := ((reverseValue length pair.1.2, reverseValue length pair.1.1), pair.2)
  invFun pair := ((reverseValue length pair.1.2, reverseValue length pair.1.1), pair.2)
  left_inv pair := by
    rcases pair with ⟨⟨source, target⟩, sign⟩
    simp only [reverseValue_twice]
  right_inv pair := by
    rcases pair with ⟨⟨source, target⟩, sign⟩
    simp only [reverseValue_twice]

/-- The oriented focus leaves the entire original complementary tuple intact. -/
def orientation {width : Nat} (window : Window width) :
    (Addition.TTK.OverflowRegisters window.length × Complement window) ≃
      (Addition.TTK.OverflowRegisters window.length × Complement window) :=
  Equiv.prodCongr (focus window.length) (Equiv.refl _)

/-- Exact coefficient grouping of the original full frame, including arbitrary outside values. -/
def grouping {width : Nat} (window : Window width) :
    Registers width ≃ (Addition.TTK.OverflowRegisters window.length × Complement window) :=
  (ArithmeticWindowRegisters.grouping window).trans (orientation window)

/-- Original Sign remains the TTK overflow output under coefficient orientation. -/
theorem grouping_sign {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).1.2 = state.flags.sign := rfl

/-- Every original non-window field is retained by the exact coefficient grouping. -/
theorem grouping_complement {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).2 = (ArithmeticWindowRegisters.grouping window state).2 := rfl

/-- The source is the actual Work1 slice, interpreted in its physical little-endian order. -/
theorem grouping_source {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).1.1.1 =
      BitVec.equivFin (state.firstWord.extractLsb' window.below window.length).reverse := by
  change reverseValue window.length
    (BitVec.equivFin (wordEquiv window state.firstWord).2.1) = _
  rw [reverseValue_word, wordEquiv_window]

/-- The target is the actual Work2 slice; no wrapped fractional suffix is part of this operand. -/
theorem grouping_target {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).1.1.2 =
      BitVec.equivFin (state.secondWord.extractLsb' window.below window.length).reverse := by
  change reverseValue window.length
    (BitVec.equivFin (wordEquiv window state.secondWord).2.1) = _
  rw [reverseValue_word, wordEquiv_window]

/-- Coefficient little-endian index zero is the first physical bit of the selected region. -/
def windowIndex {width : Nat} (window : Window width) (index : Fin window.length) :
    Fin (width + 3) :=
  ⟨window.above + index.val, by
    have complete := window.complete
    have within := index.isLt
    omega⟩

private theorem reverse_slice_bit {width : Nat} (window : Window width)
    (word : BitVec (width + 3)) (index : Fin window.length) :
    (word.extractLsb' window.below window.length).reverse.getLsbD index.val =
      word.getMsbD (windowIndex window index).val := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_extractLsb']
  have complete := window.complete
  have within := index.isLt
  have bound : window.below + window.length - index.val ≤ width + 3 := by omega
  have position : width + 3 - (window.below + window.length - index.val) =
      (windowIndex window index).val := by
    change width + 3 - (window.below + window.length - index.val) = window.above + index.val
    omega
  simp only [within, bound, decide_true, Bool.true_and, position]

/-- Every source TTK bit reads its exact original Work1 coefficient wire. -/
theorem grouping_source_bit {width : Nat} (window : Window width) (index : Fin window.length)
    (state : Registers width) :
    (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index)).get
        (grouping window state).1 =
      (firstWordBit width (windowIndex window index)).get state := by
  rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkLeftBit_get, grouping_source]
  change (state.firstWord.extractLsb' window.below window.length).reverse.getLsbD index.val = _
  exact (reverse_slice_bit window state.firstWord index).trans
    (firstWordBit_get width (windowIndex window index) state).symm

/-- Every target TTK bit reads its exact original Work2 coefficient wire. -/
theorem grouping_target_bit {width : Nat} (window : Window width) (index : Fin window.length)
    (state : Registers width) :
    (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index)).get
        (grouping window state).1 =
      (secondWordBit width (windowIndex window index)).get state := by
  rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkRightBit_get, grouping_target]
  change (state.secondWord.extractLsb' window.below window.length).reverse.getLsbD index.val = _
  exact (reverse_slice_bit window state.secondWord index).trans
    (secondWordBit_get width (windowIndex window index) state).symm

/-- Decode all oriented pieces and reassemble the actual original full-frame basis label. -/
def indexEquiv {width : Nat} (window : Window width) :
    (Qubits (groupedEncoding window).width).Index ≃ (Qubits (encoding width).width).Index :=
  (groupedLabelEquiv window).symm.trans
    ((grouping window).symm.trans (registerLabelEquiv width))

/-- The exact coefficient reassembly commutes with the complete real binary encodings. -/
theorem indexEquiv_encode {width : Nat} (window : Window width) (state : Registers width) :
    indexEquiv window ((groupedEncoding window).encode (grouping window state)) =
      (encoding width).encode state := by
  change registerLabelEquiv width ((grouping window).symm
    ((groupedLabelEquiv window).symm (groupedLabelEquiv window (grouping window state)))) =
      registerLabelEquiv width state
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowOrientation
