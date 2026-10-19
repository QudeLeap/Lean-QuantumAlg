/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest
/-! # Value-level helpers for clean encoded-word zero tests -/

section

namespace QuantumAlg.PlainAdder.Schedule.PowerOfTwo

/-- Every encoded bit of a power-of-two word known to be zero reads false. -/
lemma wordBit_get_false_of_eq_zero (n : Nat) (bit : Fin n)
    (x : QuantumAlg.PlainAdder.Word n) (hzero : x = 0) :
    (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get x = false := by
  subst x
  simp

/-- A power-of-two word is zero exactly when each of its encoded bit readouts
is false. -/
lemma all_wordBit_get_false_iff_eq_zero (n : Nat)
    (x : QuantumAlg.PlainAdder.Word n) :
    (∀ bit, (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get x =
      false) ↔ x = 0 := by
  constructor
  · intro hbits
    apply word_eq_of_testBit_eq
    intro bit
    have hbit := hbits bit
    rw [wordBit_get] at hbit
    simpa using hbit
  · intro hzero bit
    exact wordBit_get_false_of_eq_zero n bit x hzero

end QuantumAlg.PlainAdder.Schedule.PowerOfTwo

namespace QuantumAlg.EncodedBit.Word.ZeroTestLayout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}

/-- Output-only projection of the generic clean zero-test endpoint.  This
keeps fixed-width clients from instantiating the larger conjunction when they
only need the predicate bit. -/
lemma step_cleanZeroOutput
    (layout : ZeroTestLayout (encoding := encoding) tail) (x : Data)
    (hclean : ∀ j, (layout.work.bit j).get x = false) :
    layout.output.get (step layout x) =
      (layout.output.get x ^^
        decide (∀ i, (layout.source.bit i).get x = false)) :=
  (step_cleanZeroEndpoint layout x hclean).2.2

/-- Word-level output endpoint for a zero-test layout whose source lenses read
one canonical power-of-two word.  The concrete result contains no per-bit
quantifier. -/
lemma step_cleanZeroOutput_eq_decide_word_eq_zero
    (layout : ZeroTestLayout (encoding := encoding) tail) (x : Data)
    (value : QuantumAlg.PlainAdder.Word (tail + 2))
    (hclean : ∀ j, (layout.work.bit j).get x = false)
    (hsource : ∀ i, (layout.source.bit i).get x =
      (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit (tail + 2) i).get
        value) :
    layout.output.get (step layout x) =
      (layout.output.get x ^^ decide (value = 0)) := by
  rw [step_cleanZeroOutput layout x hclean]
  have hpredicate :
      (∀ i, (layout.source.bit i).get x = false) ↔ value = 0 := by
    constructor
    · intro hbits
      apply (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.all_wordBit_get_false_iff_eq_zero
        (tail + 2) value).mp
      intro bit
      rw [← hsource bit]
      exact hbits bit
    · intro hzero bit
      rw [hsource bit]
      exact QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit_get_false_of_eq_zero
        (tail + 2) bit value hzero
  have hdecide :
      decide (∀ i, (layout.source.bit i).get x = false) =
        decide (value = 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hpredicate
  rw [hdecide]

/-- Semantic output endpoint when the source word has already been identified
with a value of interest and the xor-output bit is initially clean. -/
lemma step_cleanZeroOutput_of_clean_eq_decide_word_eq_zero
    (layout : ZeroTestLayout (encoding := encoding) tail) (x : Data)
    (value semanticValue : QuantumAlg.PlainAdder.Word (tail + 2))
    (hclean : ∀ j, (layout.work.bit j).get x = false)
    (hsource : ∀ i, (layout.source.bit i).get x =
      (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit (tail + 2) i).get
        value)
    (hvalue : value = semanticValue)
    (houtput : layout.output.get x = false) :
    layout.output.get (step layout x) = decide (semanticValue = 0) := by
  rw [step_cleanZeroOutput_eq_decide_word_eq_zero
    layout x value hclean hsource]
  rw [houtput, Bool.false_xor, hvalue]

/-- Semantic zero-test endpoint whose clean-work premise is supplied as one
canonical work-word equality rather than a fixed-width family of bit proofs. -/
lemma step_cleanZeroOutput_of_word_work_eq_decide_word_eq_zero
    (layout : ZeroTestLayout (encoding := encoding) tail) (x : Data)
    (value semanticValue : QuantumAlg.PlainAdder.Word (tail + 2))
    (workValue : QuantumAlg.PlainAdder.Word tail)
    (hworkzero : workValue = 0)
    (hwork : ∀ j, (layout.work.bit j).get x =
      (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit tail j).get workValue)
    (hsource : ∀ i, (layout.source.bit i).get x =
      (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit (tail + 2) i).get
        value)
    (hvalue : value = semanticValue)
    (houtput : layout.output.get x = false) :
    layout.output.get (step layout x) = decide (semanticValue = 0) := by
  apply step_cleanZeroOutput_of_clean_eq_decide_word_eq_zero
    layout x value semanticValue
  · intro bit
    exact Eq.trans (hwork bit)
      (QuantumAlg.PlainAdder.Schedule.PowerOfTwo.wordBit_get_false_of_eq_zero
        tail bit workValue hworkzero)
  · exact hsource
  · exact hvalue
  · exact houtput

end QuantumAlg.EncodedBit.Word.ZeroTestLayout

end
