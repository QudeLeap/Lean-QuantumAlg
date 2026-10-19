/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern

/-!
# Actual divisor and complete-clock coordinates for terminal dispatch

The source already detects termination through its divisor-length field
[LYL+26, sec_EEA/sub_opt.tex:74-84]. The internal finite-counter repair
also reads the two actual Work1 positions and the original low counter.
This layout contains precisely those source wires, original Ctrl as
output, and original Iter as arbitrary restored work. It adds no wire.

The longer zero conjunction is one term in a reversible dispatch that
uses the original low counter while the divisor is nonzero, and the
complete physical counter after termination. No active high-bit zero
assumption or terminal idle instruction is part of this layout.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalPredicateLayout

noncomputable section

open EncodedBit PredicateLayout

/-- The actual complete clock followed by the original full divisor length. -/
def sourceCount (width : Nat) : Nat := width.size + 2 + width.size

/-- Every source position names a real existing original-frame bit. -/
def sourceBit (width : Nat) (index : Fin (sourceCount width)) : EncodedBit (encoding width) :=
  if clock : index.val < width.size + 2 then clockBit width ⟨index.val, clock⟩
  else divisorLengthBit width ⟨index.val - (width.size + 2), by
    have within := index.isLt
    unfold sourceCount at within
    omega⟩

private lemma clockBit_wire (width : Nat) (index : Fin (width.size + 2)) :
    (PredicateLayout.clockBit width index).wire.val =
      if index.val < 2 then width + index.val
      else 2 * (width + 3) + 3 * width.size + (index.val - 2) := by
  by_cases high : index.val < 2
  · simp only [PredicateLayout.clockBit, dif_pos high, if_pos high, paddingBit_wire]
  · simp only [PredicateLayout.clockBit, dif_neg high, if_neg high, shiftBit_wire]

private lemma clock_before_flags (width : Nat) (index : Fin (width.size + 2)) :
    (clockBit width index).wire.val < 2 * (width + 3) + 4 * width.size := by
  rw [clockBit_wire]
  have within := index.isLt
  split <;> omega

private lemma clock_divisor_ne (width : Nat) (clock : Fin (width.size + 2))
    (divisor : Fin width.size) :
    (clockBit width clock).wire ≠ (divisorLengthBit width divisor).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [clockBit_wire, divisorLengthBit_wire] at values
  have clockBound := clock.isLt
  have divisorBound := divisor.isLt
  split_ifs at values <;> omega

/-- Neither the two physical clock regions nor the divisor field duplicate a source wire. -/
lemma sourceBit_injective (width : Nat) :
    Function.Injective (fun index => (sourceBit width index).wire) := by
  intro left right same
  by_cases leftClock : left.val < width.size + 2
  · by_cases rightClock : right.val < width.size + 2
    · have selected : (clockBit width ⟨left.val, leftClock⟩).wire =
          (clockBit width ⟨right.val, rightClock⟩).wire := by
        simpa only [sourceBit, dif_pos leftClock, dif_pos rightClock] using same
      exact Fin.ext (congrArg (fun index : Fin (width.size + 2) => index.val)
        (PredicateLayout.clockBit_injective width selected))
    · have selected : (clockBit width ⟨left.val, leftClock⟩).wire =
          (divisorLengthBit width ⟨right.val - (width.size + 2), by
            have within := right.isLt
            unfold sourceCount at within
            omega⟩).wire := by
        simpa only [sourceBit, dif_pos leftClock, dif_neg rightClock] using same
      exact False.elim (clock_divisor_ne width _ _ selected)
  · by_cases rightClock : right.val < width.size + 2
    · have selected : (divisorLengthBit width ⟨left.val - (width.size + 2), by
            have within := left.isLt
            unfold sourceCount at within
            omega⟩).wire = (clockBit width ⟨right.val, rightClock⟩).wire := by
        simpa only [sourceBit, dif_neg leftClock, dif_pos rightClock] using same
      exact False.elim (clock_divisor_ne width _ _ selected.symm)
    · have values := congrArg (fun index : Fin (encoding width).width => index.val) same
      simp only [sourceBit, dif_neg leftClock, dif_neg rightClock] at values
      rw [divisorLengthBit_wire, divisorLengthBit_wire] at values
      change 2 * (width + 3) + 2 * width.size + (left.val - (width.size + 2)) =
        2 * (width + 3) + 2 * width.size + (right.val - (width.size + 2)) at values
      apply Fin.ext
      omega

/-- All read coordinates precede the five original control bits. -/
lemma sourceBit_before_flags (width : Nat) (index : Fin (sourceCount width)) :
    (sourceBit width index).wire.val < 2 * (width + 3) + 4 * width.size := by
  unfold sourceBit
  split
  · exact clock_before_flags width _
  · rw [divisorLengthBit_wire]
    have within := index.isLt
    unfold sourceCount at within
    omega

/-- A genuine one-dirty physical layout, including every original zero-width boundary. -/
def layout (width : Nat) :
    Word.OneDirtyLayout (encoding := encoding width) (sourceCount width) where
  source := ⟨sourceBit width⟩
  output := controlBit width
  work := iterationBit width
  source_injective := sourceBit_injective width
  source_output_ne := by
    intro index same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (sourceBit width index).wire.val = (controlBit width).wire.val at values
    rw [controlBit_wire] at values
    have before := sourceBit_before_flags width index
    omega
  source_work_ne := by
    intro index same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (sourceBit width index).wire.val = (iterationBit width).wire.val at values
    rw [iterationBit_wire] at values
    have before := sourceBit_before_flags width index
    omega
  work_output_ne := by
    intro same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (iterationBit width).wire.val = (controlBit width).wire.val at values
    rw [iterationBit_wire, controlBit_wire] at values
    omega

/-- Embed one actual complete-clock source without changing its coordinate. -/
def clockIndex (width : Nat) (index : Fin (width.size + 2)) : Fin (sourceCount width) :=
  ⟨index.val, by unfold sourceCount; have within := index.isLt; omega⟩

/-- Embed one actual divisor-length source after the complete clock. -/
def divisorIndex (width : Nat) (index : Fin width.size) : Fin (sourceCount width) :=
  ⟨width.size + 2 + index.val, by unfold sourceCount; have within := index.isLt; omega⟩

lemma sourceBit_clock (width : Nat) (index : Fin (width.size + 2)) :
    sourceBit width (clockIndex width index) = clockBit width index := by
  change (if inside : index.val < width.size + 2 then clockBit width ⟨index.val, inside⟩
    else _) = _
  rw [dif_pos index.isLt]

lemma sourceBit_divisor (width : Nat) (index : Fin width.size) :
    sourceBit width (divisorIndex width index) = divisorLengthBit width index := by
  have afterClock : ¬width.size + 2 + index.val < width.size + 2 := by omega
  change (if inside : width.size + 2 + index.val < width.size + 2 then _
    else divisorLengthBit width ⟨width.size + 2 + index.val - (width.size + 2), _⟩) = _
  rw [dif_neg afterClock]
  exact congrArg (divisorLengthBit width) (Fin.ext (Nat.add_sub_cancel_left _ _))

/-- The actual pattern reads exactly zero divisor and zero full physical clock. -/
lemma source_zero_iff (width : Nat) (state : Registers width) :
    (layout width).PatternMatches (fun _ => false) state ↔
      (NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0) ∧
        state.divisorLength = 0 := by
  have clockZero :
      (∀ index : Fin (width.size + 2), (clockBit width index).get state = false) ↔
        NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0 :=
    NativePredicate.clock_source_zero_iff width state
  rw [← clockZero, ← NativePredicate.word_zero_iff]
  change (∀ index : Fin (sourceCount width), (sourceBit width index).get state = false) ↔ _
  constructor
  · intro matched
    constructor
    · intro index
      have actual := matched (clockIndex width index)
      rw [sourceBit_clock] at actual
      exact actual
    · intro index
      have actual := matched (divisorIndex width index)
      rw [sourceBit_divisor, divisorLengthBit_get] at actual
      exact actual
  · rintro ⟨clockZero, divisorZero⟩ index
    unfold sourceBit
    split
    · exact clockZero _
    · rw [divisorLengthBit_get]
      exact divisorZero _

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalPredicateLayout
