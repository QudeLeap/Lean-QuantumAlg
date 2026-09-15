/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PredicateLayout

/-!
# Actual source coordinates for the dynamic Sign exchange

The source selects the Work1 position from the untruncated natural sum
of coefficient length and quotient length, under the two unequal phases
[LYL+26, sec_EEA/sub_opt.tex:52-59]. The finite selector refinement reads
exactly those two complete length fields and both phase bits. Its output
is the existing Ctrl, and its borrowed conjunction work uses existing
Work2 positions only. No assumption is made about their incoming values.

The source word has `2 * Nat.size n + 2` bits. The corresponding dirty
chain needs `2 * Nat.size n` bits, which fit inside the original `n+3`
Work2 for every width, including zero. Equality masks, actual controlled
Sign swaps, inverse cleanup, and enumeration are separate native steps.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SelectionLayout

noncomputable section

open EncodedBit

/-- Two complete lengths followed by the two original phase bits. -/
def sourceBit (width : Nat) (index : Fin (2 * width.size + 2)) : EncodedBit (encoding width) :=
  if first : index.val < width.size then coefficientLengthBit width ⟨index.val, first⟩
  else if second : index.val < 2 * width.size then
    quotientLengthBit width ⟨index.val - width.size, by omega⟩
  else if index.val = 2 * width.size then phase1Bit width else phase2Bit width

/-- The actual native identity skips only the intervening divisor/shift field blocks. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < 2 * width.size then 2 * (width + 3) + index
  else 2 * (width + 3) + 2 * width.size + index

theorem sourceBit_wire (width : Nat) (index : Fin (2 * width.size + 2)) :
    (sourceBit width index).wire.val = physicalIndex width index.val := by
  have within := index.isLt
  unfold sourceBit
  split
  · rw [coefficientLengthBit_wire]
    change 2 * (width + 3) + index.val = physicalIndex width index.val
    unfold physicalIndex
    split_ifs <;> omega
  · split
    · rw [quotientLengthBit_wire]
      change 2 * (width + 3) + width.size + (index.val - width.size) =
        physicalIndex width index.val
      unfold physicalIndex
      split_ifs
      omega
    · split
      · rw [phase1Bit_wire]
        unfold physicalIndex
        split_ifs
        omega
      · rw [phase2Bit_wire]
        unfold physicalIndex
        split_ifs
        omega

/-- The selector reads the complete actual finite length values and original phase fields. -/
theorem sourceBit_get (width : Nat) (index : Fin (2 * width.size + 2))
    (state : Registers width) :
    (sourceBit width index).get state =
      if index.val < width.size then state.coefficientLength.getMsbD index.val
      else if index.val < 2 * width.size then state.quotientLength.getMsbD (index.val - width.size)
      else if index.val = 2 * width.size then state.flags.first else state.flags.second := by
  unfold sourceBit
  split
  · exact coefficientLengthBit_get width _ state
  · split
    · exact quotientLengthBit_get width _ state
    · split <;> rfl

private theorem source_injective (width : Nat) :
    Function.Injective (fun index : Fin (2 * width.size + 2) => (sourceBit width index).wire) := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  change (sourceBit width left).wire.val = (sourceBit width right).wire.val at values
  rw [sourceBit_wire, sourceBit_wire] at values
  unfold physicalIndex at values
  split_ifs at values <;> omega

/-- The required arbitrary-work chain fits inside the original Work2 without new systems. -/
theorem work_capacity (width : Nat) : 2 * width.size ≤ width + 3 := by
  have original := PredicateLayout.pair_work_capacity width
  omega

/-- Actual all-source predicate layout using only the already allocated Ctrl and dirty Work2. -/
def layout (width : Nat) : Word.ZeroTestLayout (encoding := encoding width) (2 * width.size) :=
  PredicateLayout.fromSource width (2 * width.size) (work_capacity width)
    ⟨sourceBit width⟩ (source_injective width)
    (by
      intro index
      apply Or.inr
      change 2 * (width + 3) ≤ (sourceBit width index).wire.val
      rw [sourceBit_wire]
      unfold physicalIndex
      split_ifs <;> omega)
    (by
      intro index
      change (sourceBit width index).wire.val < (controlBit width).wire.val
      rw [sourceBit_wire, controlBit_wire]
      have within := index.isLt
      unfold physicalIndex
      split_ifs <;> omega)

/-- The native layout's source is exactly the declared two-length/two-phase readout. -/
theorem layout_source_get (width : Nat) (index : Fin (2 * width.size + 2))
    (state : Registers width) :
    ((layout width).source.bit index).get state = (sourceBit width index).get state := rfl

/-- Every arbitrary work position is an actual original Work2 position. -/
theorem layout_work_get (width : Nat) (index : Fin (2 * width.size)) (state : Registers width) :
    ((layout width).work.bit index).get state = state.secondWord.getMsbD index.val :=
  PredicateLayout.workBit_get width _ (work_capacity width) index state

/-- The xor output is the existing Ctrl field and introduces no additional register. -/
theorem layout_output_get (width : Nat) (state : Registers width) :
    (layout width).output.get state = state.control := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.SelectionLayout
