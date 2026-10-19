/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Rotation

/-!
# Exact physical coefficient-window extraction and replacement

The source acts on the left-most coefficient-length-plus-one bits of the
actually rotated second word [LYL+26, sec_EEA/sub_regshare.tex:263-264,288-296].
This owner reads those physical bits with `extractLsb'`, reverses their
little-endian order into an arithmetic word, and replaces exactly that
same region by literal concatenation. The width cast preserves the proved
bit positions; it does not choose an encoding from a cardinality equality.

Every bit outside the selected region is preserved. Reading after writing
recovers the replacement, and writing back an extracted window recovers
the complete original word. For a rotated source payload, the read window
is exactly the corresponding coefficient slice, including zero-width
regions. Reachable source capacities establish the slice-fit premise in
the concrete coefficient-phase owner.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PhysicalWindow

variable {wordWidth windowWidth coefficientWidth remainderWidth : Nat}

/-- Read the actual left-most physical region in the coefficient's arithmetic bit order. -/
def read (windowWidth : Nat) (word : BitVec wordWidth) : BitVec windowWidth :=
  (word.extractLsb' (wordWidth - windowWidth) windowWidth).reverse

/-- Replace the selected region while retaining the literal suffix of the original word. -/
def replace (word : BitVec wordWidth) (replacement : BitVec windowWidth)
    (fits : windowWidth ≤ wordWidth) : BitVec wordWidth :=
  (replacement.reverse ++ word.extractLsb' 0 (wordWidth - windowWidth)).cast (by omega)

/-- Each arithmetic window bit is exactly its physical left-to-right source bit. -/
lemma read_bit (word : BitVec wordWidth) (fits : windowWidth ≤ wordWidth)
    (index : Nat) (within : index < windowWidth) :
    (read windowWidth word).getLsbD index = word.getMsbD index := by
  have joined : wordWidth - windowWidth + windowWidth = wordWidth := by omega
  have sourceWithin : wordWidth - index ≤ wordWidth := by omega
  have sourceIndex : wordWidth - (wordWidth - index) = index := by omega
  simp only [read, BitVec.getLsbD_reverse, BitVec.getMsbD_extractLsb', joined, within,
    sourceWithin, sourceIndex, decide_true, Bool.true_and]

/-- Every replaced or retained physical bit follows the exact region boundary. -/
lemma replace_bit (word : BitVec wordWidth) (replacement : BitVec windowWidth)
    (fits : windowWidth ≤ wordWidth) (index : Nat) (within : index < wordWidth) :
    (replace word replacement fits).getMsbD index =
      if index < windowWidth then replacement.getLsbD index else word.getMsbD index := by
  by_cases inWindow : index < windowWidth
  · simp only [replace, BitVec.getMsbD_cast, BitVec.getMsbD_append,
      if_neg (Nat.not_le_of_lt inWindow), BitVec.getMsbD_reverse, if_pos inWindow]
  · have afterWindow : windowWidth ≤ index := by omega
    have tailWithin : index - windowWidth < wordWidth - windowWidth := by omega
    have sourceWithin : 0 + (wordWidth - windowWidth) - (index - windowWidth) ≤
        wordWidth := by omega
    have sourceIndex : wordWidth -
        (0 + (wordWidth - windowWidth) - (index - windowWidth)) = index := by omega
    simp only [replace, BitVec.getMsbD_cast, BitVec.getMsbD_append, if_pos afterWindow,
      BitVec.getMsbD_extractLsb', tailWithin, sourceWithin, sourceIndex,
      decide_true, Bool.true_and, if_neg inWindow]

/-- Every physical suffix bit, including wrapped low coefficient bits, is preserved exactly. -/
lemma replace_outside (word : BitVec wordWidth) (replacement : BitVec windowWidth)
    (fits : windowWidth ≤ wordWidth) (index : Nat)
    (outside : windowWidth ≤ index) (within : index < wordWidth) :
    (replace word replacement fits).getMsbD index = word.getMsbD index := by
  rw [replace_bit word replacement fits index within, if_neg (Nat.not_lt.mpr outside)]

/-- Reading the replaced physical region recovers the complete arithmetic replacement word. -/
lemma read_replace (word : BitVec wordWidth) (replacement : BitVec windowWidth)
    (fits : windowWidth ≤ wordWidth) :
    read windowWidth (replace word replacement fits) = replacement := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  rw [read_bit _ fits index within,
    replace_bit word replacement fits index (within.trans_le fits), if_pos within]

/-- Replacing a physical region by its own extracted bits preserves the entire word. -/
lemma replace_read (word : BitVec wordWidth) (fits : windowWidth ≤ wordWidth) :
    replace word (read windowWidth word) fits = word := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [replace_bit word (read windowWidth word) fits index within]
  by_cases inWindow : index < windowWidth
  · rw [if_pos inWindow, read_bit word fits index inWindow]
  · rw [if_neg inWindow]

/-- The actual rotated physical window is exactly the prescribed coefficient bit slice. -/
lemma read_rotated (shift : Nat)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (fits : shift + windowWidth ≤ coefficientWidth) :
    read windowWidth (WordRotation.packRotatedWork2 shift payload) =
      payload.coefficientBits.extractLsb' shift windowWidth := by
  have windowFits : windowWidth ≤ coefficientWidth + remainderWidth := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have physicalWithin : index < coefficientWidth + remainderWidth := by omega
  have coefficientWithin : shift + index < coefficientWidth := by omega
  have sourceWithin : shift + index < coefficientWidth + remainderWidth := by omega
  rw [read_bit _ windowFits index within, WordRotation.packRotatedWork2_bit]
  simp only [Nat.mod_eq_of_lt sourceWithin, physicalWithin, decide_true, Bool.true_and,
    if_neg (Nat.not_le_of_lt coefficientWithin), BitVec.getLsbD_extractLsb', within]

/-- No selected bits is a genuine empty window, and replacing it preserves the physical word. -/
lemma replace_empty (word : BitVec wordWidth) :
    replace word (0 : BitVec 0) (Nat.zero_le _) = word := by
  have emptyRead : read 0 word = (0 : BitVec 0) := BitVec.of_length_zero
  rw [← emptyRead]
  exact replace_read word (Nat.zero_le _)

end QuantumAlg.NumberTheory.SharedEEA.PhysicalWindow
