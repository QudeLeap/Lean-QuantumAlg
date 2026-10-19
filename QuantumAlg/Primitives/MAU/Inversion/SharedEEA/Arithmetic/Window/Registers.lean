/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Primitives.MAU.Addition.TTK.Layout

/-!
# Exact same-position work-word windows for native remainder arithmetic

The source remainder arithmetic uses aligned regions of the two work
words, excluding the wrapped coefficient bits at the right of Work2
[LYL+26, sec_EEA/sub_regshare.tex:263-278]. A compile-time window below
records its physical prefix, arithmetic region, and suffix. The complete
word is split and reassembled by literal extraction and concatenation.

The TTK operands are the Work2 source and Work1 target windows, with the
existing Sign as overflow output [TTK09, qic-loglogaddition-quant.tex:285-318].
Every outside bit, all lengths, both phases, Iter, and Ctrl are retained
in the explicit complementary tuple. No unknown padding bit is discarded
or used as a prepared zero. Selecting a window from actual finite length
keys and placing the native TTK program are subsequent constructions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowRegisters

noncomputable section

/-- Static physical geometry of one complete partition of an existing work word. -/
structure Window (width : Nat) where
  above : Nat
  length : Nat
  below : Nat
  complete : above + (length + below) = width + 3

/-- The source region from its retained left boundary through its unwrapped right boundary. -/
def remainderWindow (width start shift : Nat) (fits : start + shift ≤ width + 3) :
    Window width where
  above := start
  length := width + 3 - start - shift
  below := shift
  complete := by omega

private def splitEquiv (high low : Nat) : BitVec (high + low) ≃ (BitVec high × BitVec low) where
  toFun word := (word.extractLsb' low high, word.extractLsb' 0 low)
  invFun pair := pair.1 ++ pair.2
  left_inv _ := BitVec.extractLsb'_append_extractLsb'
  right_inv pair := by
    apply Prod.ext
    · exact BitVec.extractLsb'_append_eq_left
    · exact BitVec.extractLsb'_append_eq_right

private def castEquiv {width : Nat} (window : Window width) :
    BitVec (width + 3) ≃ BitVec (window.above + (window.length + window.below)) where
  toFun word := word.cast window.complete.symm
  invFun word := word.cast window.complete
  left_inv word := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_cast]
  right_inv word := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_cast]

/-- Exact prefix/window/suffix reassembly, valid even when any region is empty. -/
def wordEquiv {width : Nat} (window : Window width) :
    BitVec (width + 3) ≃
      (BitVec window.above × (BitVec window.length × BitVec window.below)) :=
  (castEquiv window).trans
    ((splitEquiv window.above (window.length + window.below)).trans
      (Equiv.prodCongr (Equiv.refl _) (splitEquiv window.length window.below)))

/-- The arithmetic input is the actual physical slice, not a recomputed value. -/
lemma wordEquiv_window {width : Nat} (window : Window width) (word : BitVec (width + 3)) :
    (wordEquiv window word).2.1 = word.extractLsb' window.below window.length := by
  change (((word.cast window.complete.symm).extractLsb' 0
    (window.length + window.below)).extractLsb' window.below window.length) = _
  rw [BitVec.extractLsb'_cast]
  exact BitVec.extractLsb'_extractLsb'_of_le (by omega)

/-- The complete physical prefix is retained independently of the arithmetic input. -/
lemma wordEquiv_above {width : Nat} (window : Window width) (word : BitVec (width + 3)) :
    (wordEquiv window word).1 = word.extractLsb' (window.length + window.below) window.above := by
  change (word.cast window.complete.symm).extractLsb' _ _ = _
  exact BitVec.extractLsb'_cast

/-- The complete suffix includes any wrapped coefficient fraction and is retained exactly. -/
lemma wordEquiv_below {width : Nat} (window : Window width) (word : BitVec (width + 3)) :
    (wordEquiv window word).2.2 = word.extractLsb' 0 window.below := by
  change (((word.cast window.complete.symm).extractLsb' 0
    (window.length + window.below)).extractLsb' 0 window.below) = _
  rw [BitVec.extractLsb'_cast]
  exact BitVec.extractLsb'_extractLsb'_of_le (by omega)

/-- Exact physical address of a little-endian TTK operand bit inside the selected window. -/
def windowIndex {width : Nat} (window : Window width) (index : Fin window.length) :
    Fin (width + 3) :=
  ⟨window.above + (window.length - 1 - index.val), by
    have complete := window.complete
    have within := index.isLt
    omega⟩

/-- Each arithmetic bit reads the same actual original work-word position. -/
lemma wordEquiv_window_bit {width : Nat} (window : Window width)
    (word : BitVec (width + 3)) (index : Fin window.length) :
    (wordEquiv window word).2.1.getLsbD index.val =
      word.getMsbD (windowIndex window index).val := by
  rw [wordEquiv_window, BitVec.getLsbD_extractLsb']
  have reverse : width + 3 - 1 - (windowIndex window index).val =
      window.below + index.val := by
    change width + 3 - 1 - (window.above + (window.length - 1 - index.val)) = _
    have complete := window.complete
    have within := index.isLt
    omega
  simp only [index.isLt, decide_true, Bool.true_and, BitVec.getMsbD_eq_getLsbD,
    (windowIndex window index).isLt, reverse]

/-- Every bit outside both windows and the Sign output is part of the explicit complement. -/
abbrev Complement {width : Nat} (window : Window width) :=
  (BitVec window.above × BitVec window.below) ×
    ((BitVec window.above × BitVec window.below) ×
      ((BitVec width.size × BitVec width.size) ×
        ((BitVec width.size × BitVec width.size) × ((Bool × Bool) × (Bool × Bool)))))

private lemma fin_roundtrip_word {length : Nat} (word : BitVec length) :
    BitVec.equivFin.symm (BitVec.equivFin word) = word :=
  BitVec.equivFin.toEquiv.symm_apply_apply word

private lemma word_roundtrip_fin {length : Nat} (value : Fin (2 ^ length)) :
    BitVec.equivFin (BitVec.equivFin.symm value) = value :=
  BitVec.equivFin.toEquiv.apply_symm_apply value

/-- Place the existing Work2 source, Work1 target, and Sign beside their full complement. -/
def grouping {width : Nat} (window : Window width) :
    Registers width ≃ (Addition.TTK.OverflowRegisters window.length × Complement window) where
  toFun state :=
    let left := wordEquiv window state.firstWord
    let right := wordEquiv window state.secondWord
    (((BitVec.equivFin right.2.1, BitVec.equivFin left.2.1), state.flags.sign),
      ((left.1, left.2.2), ((right.1, right.2.2),
        ((state.coefficientLength, state.quotientLength),
          ((state.divisorLength, state.shift),
            ((state.flags.first, state.flags.second), (state.flags.iteration, state.control)))))))
  invFun pair :=
    { firstWord := (wordEquiv window).symm
        (pair.2.1.1, (BitVec.equivFin.symm pair.1.1.2, pair.2.1.2))
      secondWord := (wordEquiv window).symm
        (pair.2.2.1.1, (BitVec.equivFin.symm pair.1.1.1, pair.2.2.1.2))
      coefficientLength := pair.2.2.2.1.1
      quotientLength := pair.2.2.2.1.2
      divisorLength := pair.2.2.2.2.1.1
      shift := pair.2.2.2.2.1.2
      flags := ⟨pair.2.2.2.2.2.1.1, pair.2.2.2.2.2.1.2, pair.1.2,
        pair.2.2.2.2.2.2.1⟩
      control := pair.2.2.2.2.2.2.2 }
  left_inv state := by
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iteration⟩, control⟩
    simp only [fin_roundtrip_word, Prod.eta, Equiv.symm_apply_apply]
  right_inv pair := by
    rcases pair with ⟨⟨⟨source, target⟩, sign⟩,
      ⟨⟨above1, below1⟩, ⟨⟨above2, below2⟩,
        ⟨⟨lengthT, lengthQ⟩, ⟨⟨lengthR, shift⟩, ⟨⟨p1, p2⟩, ⟨iteration, control⟩⟩⟩⟩⟩⟩⟩
    simp only [Equiv.apply_symm_apply, word_roundtrip_fin]

/-- The first TTK operand reads exactly the selected original Work2 slice. -/
lemma grouping_source {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).1.1.1.val =
      (state.secondWord.extractLsb' window.below window.length).toNat := by
  change (wordEquiv window state.secondWord).2.1.toNat = _
  rw [wordEquiv_window]

/-- The second TTK operand is exactly the selected original Work1 slice. -/
lemma grouping_target {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).1.1.2.val =
      (state.firstWord.extractLsb' window.below window.length).toNat := by
  change (wordEquiv window state.firstWord).2.1.toNat = _
  rw [wordEquiv_window]

/-- The explicit TTK overflow bit is the actual original Sign field. -/
lemma grouping_sign {width : Nat} (window : Window width) (state : Registers width) :
    (grouping window state).1.2 = state.flags.sign := rfl

/-- Source operand lenses use the actual selected Work2 wires. -/
def sourceBit {width : Nat} (window : Window width) (index : Fin window.length) :
    EncodedBit (encoding width) := secondWordBit width (windowIndex window index)

/-- Target operand lenses use the actual selected Work1 wires. -/
def targetBit {width : Nat} (window : Window width) (index : Fin window.length) :
    EncodedBit (encoding width) := firstWordBit width (windowIndex window index)

/-- The TTK source bit and the complete-frame lens agree at their exact physical coordinate. -/
lemma grouping_source_bit {width : Nat} (window : Window width) (index : Fin window.length)
    (state : Registers width) :
    (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index)).get
        (grouping window state).1 = (sourceBit window index).get state := by
  rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkLeftBit_get]
  change (wordEquiv window state.secondWord).2.1.toNat.testBit index.val = _
  change (wordEquiv window state.secondWord).2.1.getLsbD index.val = _
  exact (wordEquiv_window_bit window state.secondWord index).trans
    (secondWordBit_get width (windowIndex window index) state).symm

/-- The TTK target bit and the complete-frame lens agree at their exact physical coordinate. -/
lemma grouping_target_bit {width : Nat} (window : Window width) (index : Fin window.length)
    (state : Registers width) :
    (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index)).get
        (grouping window state).1 = (targetBit window index).get state := by
  rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkRightBit_get]
  change (wordEquiv window state.firstWord).2.1.toNat.testBit index.val = _
  change (wordEquiv window state.firstWord).2.1.getLsbD index.val = _
  exact (wordEquiv_window_bit window state.firstWord index).trans
    (firstWordBit_get width (windowIndex window index) state).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowRegisters
