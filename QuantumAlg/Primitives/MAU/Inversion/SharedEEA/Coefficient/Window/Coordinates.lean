/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Orientation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.FullCoordinates

/-!
# Complete physical coordinates of coefficient-oriented TTK gates

The same actual TTK source/target/Sign gate list is placed at the
little-endian Work1/Work2 coefficient coordinates
[LYL+26, sec_EEA/sub_regshare.tex:17,20,263-264,291-294]. Reversing the
combined two-operand index interval swaps the operands and reverses both
bit orders. All following Sign and complementary wire indices are fixed.

The complete map is proved injective and confined to the original frame,
including the actual Ctrl and arbitrary Iter wires used by dirty control.
These proofs concern placement of real elementary gates; they introduce
neither executed SWAP gates nor a permutation counted as a primitive.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowCoordinates

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowEncoding

/-- Reflection of just the two actual operand intervals; all other native slots are fixed. -/
def operandSlots (length index : Nat) : Nat :=
  if index < 2 * length then 2 * length - 1 - index else index

/-- The complete slot rearrangement has an explicit inverse, including zero-width operands. -/
lemma operandSlots_twice (length index : Nat) :
    operandSlots length (operandSlots length index) = index := by
  unfold operandSlots
  split_ifs <;> omega

/-- No two original native slots are merged by the operand orientation. -/
lemma operandSlots_injective (length : Nat) : Function.Injective (operandSlots length) := by
  intro left right same
  calc
    left = operandSlots length (operandSlots length left) := (operandSlots_twice length left).symm
    _ = operandSlots length (operandSlots length right) := congrArg (operandSlots length) same
    _ = right := operandSlots_twice length right

/-- The oriented slot is still in the same actual complete grouped frame. -/
lemma operandSlots_within {width : Nat} (window : Window width)
    (index : Fin (groupedEncoding window).width) :
    operandSlots window.length index.val < (groupedEncoding window).width := by
  have bound := index.isLt
  have focusBound : 2 * window.length ≤ (groupedEncoding window).width := by
    change 2 * window.length ≤ (window.length + window.length + 1) + _
    omega
  unfold operandSlots
  split_ifs <;> omega

/-- The complete original-frame coordinate of every coefficient-native and complementary slot. -/
def physicalIndex {width : Nat} (window : Window width) (index : Nat) : Nat :=
  ArithmeticWindowFullCoordinates.physicalIndex window (operandSlots window.length index)

/-- The actual coefficient placement is injective on the entire real grouped carrier. -/
lemma physicalIndex_injective {width : Nat} (window : Window width) :
    Function.Injective
      (fun index : Fin (groupedEncoding window).width => physicalIndex window index.val) := by
  intro left right same
  change ArithmeticWindowFullCoordinates.physicalIndex window
    (operandSlots window.length left.val) =
    ArithmeticWindowFullCoordinates.physicalIndex window (operandSlots window.length right.val)
    at same
  have slots := ArithmeticWindowFullCoordinates.physicalIndex_injective window
    (a₁ := ⟨operandSlots window.length left.val, operandSlots_within window left⟩)
    (a₂ := ⟨operandSlots window.length right.val, operandSlots_within window right⟩) same
  have values := congrArg (fun index : Fin (groupedEncoding window).width => index.val) slots
  apply Fin.ext
  exact operandSlots_injective window.length values

/-- Every coefficient gate and arbitrary-work control wire remains in the original frame. -/
lemma physicalIndex_within {width : Nat} (window : Window width)
    (index : Fin (groupedEncoding window).width) :
    physicalIndex window index.val < (encoding width).width :=
  ArithmeticWindowFullCoordinates.physicalIndex_within window
    ⟨operandSlots window.length index.val, operandSlots_within window index⟩

/-- Reflect only the two operand intervals as a complete permutation of grouped wires. -/
def operandWireEquiv {width : Nat} (window : Window width) :
    Fin (groupedEncoding window).width ≃ Fin (groupedEncoding window).width where
  toFun index := ⟨operandSlots window.length index.val, operandSlots_within window index⟩
  invFun index := ⟨operandSlots window.length index.val, operandSlots_within window index⟩
  left_inv index := Fin.ext (operandSlots_twice window.length index.val)
  right_inv index := Fin.ext (operandSlots_twice window.length index.val)

/-- Every coefficient-native wire is mapped through the proven original-frame bijection. -/
def wireEquiv {width : Nat} (window : Window width) :
    Fin (groupedEncoding window).width ≃ Fin (encoding width).width :=
  (operandWireEquiv window).trans (ArithmeticWindowFullCoordinates.wireEquiv window)

lemma wireEquiv_val {width : Nat} (window : Window width)
    (index : Fin (groupedEncoding window).width) :
    (wireEquiv window index).val = physicalIndex window index.val := rfl

/-- TTK source bit `i` is physically the original Work1 coefficient bit `above + i`. -/
lemma physicalIndex_source {width : Nat} (window : Window width) (index : Fin window.length) :
    physicalIndex window (window.length - 1 - index.val) = window.above + index.val := by
  have within := index.isLt
  have complete := window.complete
  unfold physicalIndex operandSlots ArithmeticWindowFullCoordinates.physicalIndex
    ArithmeticWindowCoordinates.physicalIndex
  split_ifs <;> omega

/-- TTK target bit `i` is physically the original Work2 coefficient bit `above + i`. -/
lemma physicalIndex_target {width : Nat} (window : Window width) (index : Fin window.length) :
    physicalIndex window (window.length + (window.length - 1 - index.val)) =
      width + 3 + window.above + index.val := by
  have within := index.isLt
  have complete := window.complete
  unfold physicalIndex operandSlots ArithmeticWindowFullCoordinates.physicalIndex
    ArithmeticWindowCoordinates.physicalIndex
  split_ifs <;> omega

/-- Sign remains the real original Sign wire, outside the reflected operand interval. -/
lemma physicalIndex_sign {width : Nat} (window : Window width) :
    physicalIndex window (2 * window.length) = (signBit width).wire.val := by
  rw [signBit_wire]
  unfold physicalIndex operandSlots ArithmeticWindowFullCoordinates.physicalIndex
    ArithmeticWindowCoordinates.physicalIndex
  split_ifs <;> omega

/-- Existing Ctrl is fixed by orientation and maps to the already proved original Ctrl wire. -/
lemma physicalIndex_control {width : Nat} (window : Window width) :
    physicalIndex window (ArithmeticWindowEncoding.controlBit window).wire.val =
      (SharedEEA.controlBit width).wire.val := by
  have afterOperands : 2 * window.length ≤
      (ArithmeticWindowEncoding.controlBit window).wire.val := by
    rw [ArithmeticWindowFullCoordinates.control_wire]
    omega
  rw [physicalIndex, operandSlots, if_neg (Nat.not_lt.mpr afterOperands)]
  exact ArithmeticWindowFullCoordinates.physicalIndex_control window

/-- The arbitrary Iter wire is fixed by orientation and retains its true original address. -/
lemma physicalIndex_work {width : Nat} (window : Window width) :
    physicalIndex window (workBit window).wire.val = (iterationBit width).wire.val := by
  have afterOperands : 2 * window.length ≤ (workBit window).wire.val := by
    rw [ArithmeticWindowFullCoordinates.work_wire]
    omega
  rw [physicalIndex, operandSlots, if_neg (Nat.not_lt.mpr afterOperands)]
  exact ArithmeticWindowFullCoordinates.physicalIndex_work window

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowCoordinates
