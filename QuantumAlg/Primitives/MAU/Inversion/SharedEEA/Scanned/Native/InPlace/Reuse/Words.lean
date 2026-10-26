/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse.Ports
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Numerical saved-word orientation of the actual A/Y workspace reuse

The first original A wire represents its least significant numerical
bit, whereas the first Y wire represents Y's most significant bit.
The complete physical reuse therefore reverses these numerical words.
All results are symbolic in width, including the empty word.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse

noncomputable section

open BinaryLabelEncoding

def largeWord {width : Nat} (state : OutputCopy.Data width) : Fin (2 ^ width) :=
  BitVec.equivFin (state.1.1.firstWord.reverse.setWidth width)

def reverseWord {width : Nat} (word : Fin (2 ^ width)) : Fin (2 ^ width) :=
  BitVec.equivFin (BitVec.ofFin word).reverse

lemma reverseWord_reverseWord {width : Nat} (word : Fin (2 ^ width)) :
    reverseWord (reverseWord word) = word := by
  simp only [reverseWord, BitVec.equivFin_apply, BitVec.ofFin_toFin,
    BitVec.reverse_reverse_eq]

private lemma identity_read (width : Nat) (word : Fin (2 ^ width)) (index : Fin width) :
    (finIdentityBit width index).get word = (BitVec.ofFin word).getMsbD index.val := by
  change word.val.testBit (WireAddress.bitIndex index).val = _
  rw [WireAddress.bitIndex_val, BitVec.getMsbD_eq_getLsbD]
  simp only [index.isLt, decide_true, Bool.true_and]
  rfl

/-- The saved Y word is the reversed numerical value on the reused original A payload. -/
lemma grouping_largeWord (width : Nat) (state : OutputCopy.Data width) :
    largeWord ((placement width).grouping state) = reverseWord state.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  change (((placement width).grouping state).1.1.firstWord.reverse.setWidth width).getLsbD
    index.val = ((BitVec.ofFin state.2).reverse).getLsbD index.val
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse, BitVec.getLsbD_reverse]
  simp only [index.isLt, decide_true, Bool.true_and]
  exact (grouping_large_bit width state index).trans (identity_read width state.2 index)

/-- The complementary Y label retains the reversed numerical value of the original A payload. -/
lemma grouping_numerator (width : Nat) (state : OutputCopy.Data width) :
    ((placement width).grouping state).2 = reverseWord (largeWord state) := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  let physical := WireAddress.littleEndianWire index
  have actual := grouping_numerator_bit width state physical
  have read : (finIdentityBit width physical).get ((placement width).grouping state).2 =
      (((placement width).grouping state).2).val.testBit index.val := by
    change (((placement width).grouping state).2).val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
    rw [WireAddress.bitIndex_littleEndianWire]
  rw [read] at actual
  change _ = ((BitVec.ofFin (largeWord state)).reverse).getLsbD index.val
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  simp only [index.isLt, decide_true, Bool.true_and]
  change _ = (state.1.1.firstWord.reverse.setWidth width).getLsbD (width - 1 - index.val)
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  have within : width - 1 - index.val < width := by omega
  simp only [within, decide_true, Bool.true_and]
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse
