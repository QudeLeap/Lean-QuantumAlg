/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Predicate.Layout

/-!
# Actual boundary conjunction coordinates with optional complete-clock bits

The source boundary reads quotient and shift zero after the ordered phase
updates [LYL+26, sec_EEA/sub_regshare.tex:303-315]. The finite-counter repair
also reads divisor length and, in its terminal conjunction, both actual
Work1 high bits. The layouts below supply precisely these original wires.

The source order is quotient, low shift, divisor, and optionally the two
physical high bits. Original Ctrl is the output, and arbitrary original
Iter is the restored work. Neither layout allocates storage or assumes
that active high bits are zero. The complete actual pattern gates and
their Boolean XOR combination belong to the boundary predicate owner.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.BoundaryPredicateLayout

noncomputable section

open EncodedBit

/-- Three complete original finite fields and optionally the two original high-clock positions. -/
def sourceCount (width : Nat) (withHigh : Bool) : Nat :=
  3 * width.size + if withHigh then 2 else 0

private lemma sourceCount_bound (width : Nat) (withHigh : Bool) :
    sourceCount width withHigh ≤ 3 * width.size + 2 := by
  cases withHigh <;> simp [sourceCount]

/-- Every source refers to its actual original finite field, with no arithmetic index truncation. -/
def sourceBit (width : Nat) (withHigh : Bool) (index : Fin (sourceCount width withHigh)) :
    EncodedBit (encoding width) :=
  if quotient : index.val < width.size then quotientLengthBit width ⟨index.val, quotient⟩
  else if low : index.val < 2 * width.size then
    shiftBit width ⟨index.val - width.size, by omega⟩
  else if divisor : index.val < 3 * width.size then
    divisorLengthBit width ⟨index.val - 2 * width.size, by omega⟩
  else paddingBit width ⟨index.val - 3 * width.size, by
    have within := index.isLt
    have total := sourceCount_bound width withHigh
    omega⟩

/-- Literal original wire positions of the selected source, including the true Work1 high bits. -/
lemma sourceBit_wire (width : Nat) (withHigh : Bool)
    (index : Fin (sourceCount width withHigh)) :
    (sourceBit width withHigh index).wire.val =
      if index.val < width.size then 2 * (width + 3) + width.size + index.val
      else if index.val < 2 * width.size then
        2 * (width + 3) + 3 * width.size + (index.val - width.size)
      else if index.val < 3 * width.size then
        2 * (width + 3) + 2 * width.size + (index.val - 2 * width.size)
      else width + (index.val - 3 * width.size) := by
  by_cases quotient : index.val < width.size
  · simp only [sourceBit, dif_pos quotient, if_pos quotient, quotientLengthBit_wire]
  · by_cases low : index.val < 2 * width.size
    · simp only [sourceBit, dif_neg quotient, if_neg quotient, dif_pos low, if_pos low,
        shiftBit_wire]
    · by_cases divisor : index.val < 3 * width.size
      · simp only [sourceBit, dif_neg quotient, if_neg quotient, dif_neg low, if_neg low,
          dif_pos divisor, if_pos divisor, divisorLengthBit_wire]
      · simp only [sourceBit, dif_neg quotient, if_neg quotient, dif_neg low, if_neg low,
          dif_neg divisor, if_neg divisor, paddingBit_wire]

/-- All actual source positions are distinct, even at zero-length field boundaries. -/
lemma sourceBit_injective (width : Nat) (withHigh : Bool) :
    Function.Injective (fun index => (sourceBit width withHigh index).wire) := by
  intro left right same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [sourceBit_wire, sourceBit_wire] at values
  have leftBound := left.isLt
  have rightBound := right.isLt
  have total := sourceCount_bound width withHigh
  apply Fin.ext
  split_ifs at values <;> omega

/-- Every actual source lies before the original phase, Sign, Iter, and Ctrl coordinates. -/
lemma sourceBit_before_flags (width : Nat) (withHigh : Bool)
    (index : Fin (sourceCount width withHigh)) :
    (sourceBit width withHigh index).wire.val < 2 * (width + 3) + 4 * width.size := by
  rw [sourceBit_wire]
  have within := index.isLt
  have total := sourceCount_bound width withHigh
  split_ifs <;> omega

/-- Both boundary conjunctions use the original output and one original arbitrary dirty bit. -/
def layout (width : Nat) (withHigh : Bool) :
    Word.OneDirtyLayout (encoding := encoding width) (sourceCount width withHigh) where
  source := ⟨sourceBit width withHigh⟩
  output := controlBit width
  work := iterationBit width
  source_injective := sourceBit_injective width withHigh
  source_output_ne := by
    intro index same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (sourceBit width withHigh index).wire.val = (controlBit width).wire.val at values
    rw [controlBit_wire] at values
    have before := sourceBit_before_flags width withHigh index
    omega
  source_work_ne := by
    intro index same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (sourceBit width withHigh index).wire.val = (iterationBit width).wire.val at values
    rw [iterationBit_wire] at values
    have before := sourceBit_before_flags width withHigh index
    omega
  work_output_ne := by
    intro same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (iterationBit width).wire.val = (controlBit width).wire.val at values
    rw [iterationBit_wire, controlBit_wire] at values
    omega

/-- Exact actual quantum values of all original boundary sources in their specified order. -/
lemma sourceBit_get (width : Nat) (withHigh : Bool)
    (index : Fin (sourceCount width withHigh)) (state : Registers width) :
    (sourceBit width withHigh index).get state =
      if index.val < width.size then state.quotientLength.getMsbD index.val
      else if index.val < 2 * width.size then state.shift.getMsbD (index.val - width.size)
      else if index.val < 3 * width.size then
        state.divisorLength.getMsbD (index.val - 2 * width.size)
      else (NumberTheory.SharedEEA.PaddingClock.high state.firstWord).getMsbD
        (index.val - 3 * width.size) := by
  by_cases quotient : index.val < width.size
  · simp only [sourceBit, dif_pos quotient, if_pos quotient, quotientLengthBit_get]
  · by_cases low : index.val < 2 * width.size
    · simp only [sourceBit, dif_neg quotient, if_neg quotient, dif_pos low, if_pos low,
        shiftBit_get]
    · by_cases divisor : index.val < 3 * width.size
      · simp only [sourceBit, dif_neg quotient, if_neg quotient, dif_neg low, if_neg low,
          dif_pos divisor, if_pos divisor, divisorLengthBit_get]
      · simp only [sourceBit, dif_neg quotient, if_neg quotient, dif_neg low, if_neg low,
          dif_neg divisor, if_neg divisor, paddingBit_get]

end

end QuantumAlg.MAU.Inversion.SharedEEA.BoundaryPredicateLayout
