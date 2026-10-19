/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.PaddingClock

/-!
# Exact large-workspace constant masks with the two high clock bits retained

Work1's original physical order separates the first n positions, the
two high-counter positions, and the final bit. The terminal first and
last parts are fixed by the prime-input EEA invariant; its two counter
bits retain the actual displacement history
[LYL+26, sec_EEA/sub_regshare.tex:16-23;
LYL+26, sec_point_add/sec_point_add.tex:51-79].

These are finite-word identities for the real constant-X masks. Native
gate lists and their costs are owned by the corresponding physical
programs. No extra clean field or discarded history is part of a lemma.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.WordUnloading

open PaddingClock

variable {width : Nat}

/-- The three existing physical regions reassemble the exact full first word. -/
lemma reassemble (word : BitVec (width + 3)) :
    ((main word ++ high word) ++ last word) = word := by
  have actual := congrArg Prod.fst (join_split (word, (0#0 : BitVec 0)))
  simpa only [join, split, BitVec.extractLsb'_append_eq_left] using actual

/-- A fixed mask on the main region has no set bits in either counter or final-bit region. -/
def mainMask (value : BitVec width) : BitVec (width + 3) :=
  (value ++ 0#2) ++ 0#1

/-- Main-mask projection is the exact untruncated supplied finite value. -/
lemma main_mainMask (value : BitVec width) : main (mainMask value) = value := by
  simp only [mainMask, main, BitVec.extractLsb'_append_eq_left]

/-- Both retained high clock positions have zero mask bits. -/
lemma high_mainMask (value : BitVec width) : high (mainMask value) = 0#2 := by
  simp only [mainMask, high, BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_append_eq_right]

/-- The separate last physical bit also has zero main-mask coefficient. -/
lemma last_mainMask (value : BitVec width) : last (mainMask value) = 0#1 := by
  simp only [mainMask, last, BitVec.extractLsb'_append_eq_right]

/-- Full finite XOR induces the same XOR on the complete main region. -/
lemma main_xor (left right : BitVec (width + 3)) :
    main (left ^^^ right) = main left ^^^ main right := by
  simp only [main, BitVec.extractLsb'_xor]

/-- Full finite XOR induces the same XOR on the two exact retained positions. -/
lemma high_xor (left right : BitVec (width + 3)) :
    high (left ^^^ right) = high left ^^^ high right := by
  simp only [high, BitVec.extractLsb'_xor]

/-- Full finite XOR induces the same XOR on the separate final bit. -/
lemma last_xor (left right : BitVec (width + 3)) :
    last (left ^^^ right) = last left ^^^ last right := by
  simp only [last, BitVec.extractLsb'_xor]

/-- Main-mask unloading clears exactly the main value and preserves the other physical regions. -/
lemma unload_main (word : BitVec (width + 3)) :
    main (word ^^^ mainMask (main word)) = 0#width ∧
      high (word ^^^ mainMask (main word)) = high word ∧
      last (word ^^^ mainMask (main word)) = last word := by
  simp only [main_xor, high_xor, last_xor, main_mainMask,
    high_mainMask, last_mainMask, BitVec.xor_self, BitVec.xor_zero, and_self]

/-- A second application of the same real constant mask restores the entire initial word. -/
lemma reload_main (word : BitVec (width + 3)) :
    (word ^^^ mainMask (main word)) ^^^ mainMask (main word) = word := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Matching main and final values clear both complete regions while retaining all high bits. -/
lemma unload_terminal (modulus : Nat) (word : BitVec (modulus.size + 3))
    (sameMain : main word = main (TerminalPadding.terminalWord modulus))
    (sameLast : last word = last (TerminalPadding.terminalWord modulus)) :
    word ^^^ TerminalPadding.terminalWord modulus =
      ((0#modulus.size ++ high word) ++ 0#1) := by
  have zeroMain : main (word ^^^ TerminalPadding.terminalWord modulus) = 0#modulus.size := by
    rw [main_xor, sameMain, BitVec.xor_self]
  have retained : high (word ^^^ TerminalPadding.terminalWord modulus) = high word := by
    rw [high_xor, high_terminalWord]
    change high word ^^^ 0#2 = high word
    exact BitVec.xor_zero
  have zeroLast : last (word ^^^ TerminalPadding.terminalWord modulus) = 0#1 := by
    rw [last_xor, sameLast, BitVec.xor_self]
  exact (reassemble (word ^^^ TerminalPadding.terminalWord modulus)).symm.trans
    (by rw [zeroMain, retained, zeroLast])

/-- Each of the first n physical positions is the same actual bit of the main projection. -/
lemma main_bit (word : BitVec (width + 3)) (index : Nat) (within : index < width) :
    word.getMsbD index = (main word).getMsbD index := by
  calc
    _ = (((main word ++ high word) ++ last word)).getMsbD index :=
      congrArg (fun value : BitVec (width + 3) => value.getMsbD index) (reassemble word).symm
    _ = _ := by
      simp only [BitVec.getMsbD_append, if_neg (show ¬width + 2 ≤ index by omega),
        if_neg (show ¬width ≤ index by omega)]

end QuantumAlg.NumberTheory.SharedEEA.WordUnloading
