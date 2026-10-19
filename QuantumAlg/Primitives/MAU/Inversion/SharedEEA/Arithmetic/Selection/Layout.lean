/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern

/-!
# Actual length-and-phase coordinates for location-controlled arithmetic

The selector reads complete coefficient, quotient, divisor, and low-shift
length fields, followed by the two original phase bits. Low arithmetic
may additionally read Sign. Signed arithmetic must omit Sign because
its actual body changes that value
[LYL+26, sec_EEA/sub_opt.tex:43-48,61-66]. The divisor boundary
is read for the complete fourth-phase coefficient comparison
[LYL+26, sec_EEA/sub_regshare.tex:263-264,297-300].

The output is the existing Ctrl, and the only external borrowed work is
the existing arbitrary Iter. The proven one-dirty construction permits
all original widths, without requiring a long work-word prefix or any
initialized source value. Exact finite pattern gates and actual arithmetic
placement use this same concrete source layout.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelectionLayout

noncomputable section

open EncodedBit

/-- Four actual full length words, both phases, and optionally the retained Sign bit. -/
def sourceCount (width : Nat) (includeSign : Bool) : Nat :=
  4 * width.size + 2 + if includeSign then 1 else 0

private lemma sourceCount_bound (width : Nat) (includeSign : Bool) :
    sourceCount width includeSign ≤ 4 * width.size + 3 := by
  cases includeSign <;> simp [sourceCount]

/-- Actual contiguous source lenses include the divisor boundary without truncating any field. -/
def sourceBit (width : Nat) (includeSign : Bool)
    (index : Fin (sourceCount width includeSign)) : EncodedBit (encoding width) :=
  if first : index.val < width.size then coefficientLengthBit width ⟨index.val, first⟩
  else if second : index.val < 2 * width.size then
    quotientLengthBit width ⟨index.val - width.size, by omega⟩
  else if third : index.val < 3 * width.size then
    divisorLengthBit width ⟨index.val - 2 * width.size, by omega⟩
  else if fourth : index.val < 4 * width.size then
    shiftBit width ⟨index.val - 3 * width.size, by omega⟩
  else if index.val = 4 * width.size then phase1Bit width
  else if index.val = 4 * width.size + 1 then phase2Bit width
  else signBit width

/-- The four length fields and following source flags form one contiguous physical region. -/
def physicalIndex (width index : Nat) : Nat := 2 * (width + 3) + index

/-- Each selector source lens occupies exactly its stated original physical coordinate. -/
lemma sourceBit_wire (width : Nat) (includeSign : Bool)
    (index : Fin (sourceCount width includeSign)) :
    (sourceBit width includeSign index).wire.val = physicalIndex width index.val := by
  have within := index.isLt
  have total := sourceCount_bound width includeSign
  unfold sourceBit
  split
  · exact coefficientLengthBit_wire width _
  · split
    · rw [quotientLengthBit_wire]
      change 2 * (width + 3) + width.size + (index.val - width.size) =
        2 * (width + 3) + index.val
      omega
    · split
      · rw [divisorLengthBit_wire]
        change 2 * (width + 3) + 2 * width.size + (index.val - 2 * width.size) =
          2 * (width + 3) + index.val
        omega
      · split
        · rw [shiftBit_wire]
          change 2 * (width + 3) + 3 * width.size + (index.val - 3 * width.size) =
            2 * (width + 3) + index.val
          omega
        · split
          · rw [phase1Bit_wire]
            unfold physicalIndex
            omega
          · split
            · rw [phase2Bit_wire]
              unfold physicalIndex
              omega
            · rw [signBit_wire]
              unfold physicalIndex
              omega

/-- Every source read uses actual length and phase values, including their leading zeros. -/
lemma sourceBit_get (width : Nat) (includeSign : Bool)
    (index : Fin (sourceCount width includeSign)) (state : Registers width) :
    (sourceBit width includeSign index).get state =
      if index.val < width.size then state.coefficientLength.getMsbD index.val
      else if index.val < 2 * width.size then state.quotientLength.getMsbD (index.val - width.size)
      else if index.val < 3 * width.size then
        state.divisorLength.getMsbD (index.val - 2 * width.size)
      else if index.val < 4 * width.size then state.shift.getMsbD (index.val - 3 * width.size)
      else if index.val = 4 * width.size then state.flags.first
      else if index.val = 4 * width.size + 1 then state.flags.second
      else state.flags.sign := by
  unfold sourceBit
  split
  · exact coefficientLengthBit_get width _ state
  · split
    · exact quotientLengthBit_get width _ state
    · split
      · exact divisorLengthBit_get width _ state
      · split
        · exact shiftBit_get width _ state
        · split
          · rfl
          · split <;> rfl

private lemma source_injective (width : Nat) (includeSign : Bool) :
    Function.Injective
      (fun index : Fin (sourceCount width includeSign) =>
        (sourceBit width includeSign index).wire) := by
  intro left right same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  rw [sourceBit_wire, sourceBit_wire] at values
  apply Fin.ext
  unfold physicalIndex at values
  omega

private lemma source_before_work (width : Nat) (includeSign : Bool)
    (index : Fin (sourceCount width includeSign)) :
    (sourceBit width includeSign index).wire.val < (iterationBit width).wire.val := by
  rw [sourceBit_wire, iterationBit_wire]
  have within := index.isLt
  have total := sourceCount_bound width includeSign
  unfold physicalIndex
  omega

private lemma work_before_output (width : Nat) :
    (iterationBit width).wire.val < (controlBit width).wire.val := by
  rw [iterationBit_wire, controlBit_wire]
  omega

/-- Real source coordinates, actual Ctrl output, and only the existing arbitrary Iter as work. -/
def layout (width : Nat) (includeSign : Bool) :
    Word.OneDirtyLayout (encoding := encoding width) (sourceCount width includeSign) where
  source := ⟨sourceBit width includeSign⟩
  output := controlBit width
  work := iterationBit width
  source_injective := source_injective width includeSign
  source_output_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
    exact (Nat.ne_of_lt ((source_before_work width includeSign index).trans
      (work_before_output width))) values
  source_work_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
    exact (Nat.ne_of_lt (source_before_work width includeSign index)) values
  work_output_ne := by
    intro same
    exact (Nat.ne_of_lt (work_before_output width))
      (congrArg (fun wire : Fin (encoding width).width => wire.val) same)

/-- The actual equality output is the existing source Ctrl field. -/
lemma layout_output_get (width : Nat) (includeSign : Bool) (state : Registers width) :
    (layout width includeSign).output.get state = state.control := rfl

/-- The sole arbitrary predicate work bit is the existing iteration-parity field. -/
lemma layout_work_get (width : Nat) (includeSign : Bool) (state : Registers width) :
    (layout width includeSign).work.get state = state.flags.iteration := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelectionLayout
