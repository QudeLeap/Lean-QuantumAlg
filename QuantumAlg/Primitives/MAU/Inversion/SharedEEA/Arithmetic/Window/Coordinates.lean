/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Registers

/-!
# Native TTK addresses inside both actual shared-word windows

Every TTK source address lies in the selected Work2 region, every target
address lies in the corresponding Work1 region, and the overflow address
is the existing Sign. The complete injection is proved for every static
window, including an empty window. The suffix containing wrapped low
coefficient bits is outside the addressed operand regions
[LYL+26, sec_EEA/sub_regshare.tex:263-278;
TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowCoordinates

noncomputable section

open ArithmeticWindowRegisters

/-- Explicit big-endian physical placement of the existing TTK two-word/Sign interface. -/
def physicalIndex {width : Nat} (window : Window width) (index : Nat) : Nat :=
  if index < window.length then width + 3 + window.above + index
  else if index < 2 * window.length then window.above + (index - window.length)
  else 2 * (width + 3) + 4 * width.size + 2

/-- A native little-endian source bit is exactly its original Work2 address. -/
theorem physicalIndex_source {width : Nat} (window : Window width)
    (index : Fin window.length) :
    physicalIndex window
        (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index)).wire.val =
      (sourceBit window index).wire.val := by
  change physicalIndex window (window.length - 1 - index.val) =
    (secondWordBit width (windowIndex window index)).wire.val
  rw [secondWordBit_wire]
  have within : window.length - 1 - index.val < window.length := by
    have bound := index.isLt
    omega
  rw [physicalIndex, if_pos within]
  change width + 3 + window.above + (window.length - 1 - index.val) =
    width + 3 + (window.above + (window.length - 1 - index.val))
  omega

/-- A native little-endian target bit is exactly its original Work1 address. -/
theorem physicalIndex_target {width : Nat} (window : Window width)
    (index : Fin window.length) :
    physicalIndex window
        (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index)).wire.val =
      (targetBit window index).wire.val := by
  change physicalIndex window (window.length + (window.length - 1 - index.val)) =
    (firstWordBit width (windowIndex window index)).wire.val
  rw [firstWordBit_wire]
  have initial : ¬window.length + (window.length - 1 - index.val) < window.length := by omega
  have second : window.length + (window.length - 1 - index.val) < 2 * window.length := by
    have bound := index.isLt
    omega
  rw [physicalIndex, if_neg initial, if_pos second, Nat.add_sub_cancel_left]
  rfl

/-- The native carry/borrow output is the existing Sign, not a newly allocated bit. -/
theorem physicalIndex_sign {width : Nat} (window : Window width) :
    physicalIndex window (Addition.TTK.overflowBit window.length).wire.val =
      (signBit width).wire.val := by
  change physicalIndex window (window.length + window.length) = _
  rw [signBit_wire]
  have initial : ¬window.length + window.length < window.length := by omega
  have second : ¬window.length + window.length < 2 * window.length := by omega
  rw [physicalIndex, if_neg initial, if_neg second]

/-- No source, target, or output wire aliases another native operand address. -/
theorem physicalIndex_injective {width : Nat} (window : Window width) :
    Function.Injective
      (fun index : Fin (2 * window.length + 1) => physicalIndex window index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  have complete := window.complete
  change physicalIndex window left.val = physicalIndex window right.val at same
  unfold physicalIndex at same
  split_ifs at same <;> omega

/-- Every native operand address belongs to the original full source frame. -/
theorem physicalIndex_within {width : Nat} (window : Window width)
    (index : Fin (2 * window.length + 1)) :
    physicalIndex window index.val < (encoding width).width := by
  rw [encoding_width]
  have bound := index.isLt
  have complete := window.complete
  unfold physicalIndex
  split_ifs <;> omega

/-- A Work1 suffix bit beyond the region cannot be a target of the mapped arithmetic. -/
theorem target_before_suffix {width : Nat} (window : Window width)
    (index : Fin window.length) :
    (targetBit window index).wire.val < width + 3 - window.below := by
  change (firstWordBit width (windowIndex window index)).wire.val < _
  rw [firstWordBit_wire]
  change window.above + (window.length - 1 - index.val) < _
  have complete := window.complete
  have within := index.isLt
  omega

/-- Every Work2 source bit precedes the suffix holding the wrapped coefficient fraction. -/
theorem source_before_suffix {width : Nat} (window : Window width)
    (index : Fin window.length) :
    (sourceBit window index).wire.val < 2 * (width + 3) - window.below := by
  change (secondWordBit width (windowIndex window index)).wire.val < _
  rw [secondWordBit_wire]
  change width + 3 + (window.above + (window.length - 1 - index.val)) < _
  have complete := window.complete
  have within := index.isLt
  omega

/-- Neither operand contains any physical prefix bit before its selected region. -/
theorem operands_after_prefix {width : Nat} (window : Window width)
    (index : Fin window.length) :
    window.above ≤ (targetBit window index).wire.val ∧
      width + 3 + window.above ≤ (sourceBit window index).wire.val := by
  change window.above ≤ (firstWordBit width (windowIndex window index)).wire.val ∧
    width + 3 + window.above ≤ (secondWordBit width (windowIndex window index)).wire.val
  rw [firstWordBit_wire, secondWordBit_wire]
  change window.above ≤ window.above + (window.length - 1 - index.val) ∧
    width + 3 + window.above ≤ width + 3 + (window.above + (window.length - 1 - index.val))
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowCoordinates
