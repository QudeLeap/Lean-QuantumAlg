/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Word
import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# Intrinsic operands for the Euclidean GCD circuit

The two machine words encode the existing total GCD problem, including zero
operands and width zero. The native division instruction's remainder agrees
with the ordinary Euclidean recurrence even when the divisor is zero. Neither
representation nor its arithmetic bridge imposes a new input condition.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

/-- Actual pair of equal-width unsigned operand cells. -/
abbrev operandShape (width : Nat) : CShape :=
  .product (.unsignedWord width) (.unsignedWord width)

/-- Encode the two intrinsic operands without computing through a read reference. -/
def encodeOperands {width : Nat}
    (input : ClassicalAlgorithms.NumberTheory.GCD.Input width) :
    (operandShape width).Value :=
  .product (encodeWord input.left) (encodeWord input.right)

/-- Decode the actual product representation into the total mathematical input. -/
def decodeOperands {width : Nat} (input : (operandShape width).Value) :
    ClassicalAlgorithms.NumberTheory.GCD.Input width where
  left := decodeWord input.first
  right := decodeWord input.second

@[simp] lemma gcdOperands_decode_encode {width : Nat}
    (input : ClassicalAlgorithms.NumberTheory.GCD.Input width) :
    decodeOperands (encodeOperands input) = input := by
  cases input
  rfl

@[simp] lemma gcdOperands_encode_decode {width : Nat}
    (input : (operandShape width).Value) :
    encodeOperands (decodeOperands input) = input := by
  cases input with
  | product left right =>
      cases left
      cases right
      rfl

/-- Read the natural state of the established Euclidean recurrence. -/
def decodeEuclidState {width : Nat} (first second : CShape.Word width) :
    ClassicalAlgorithms.NumberTheory.Euclid.State where
  first := first.toNat
  second := second.toNat

/-- The native remainder has no extra wrap, including for a zero divisor. -/
lemma gcdOperands_divRem_remainder {width : Nat}
    (first second : CShape.Word width) :
    (CShape.divRem width width (.product second first)).second.toNat =
      second.toNat % first.toNat := by
  change (second.toNat % first.toNat) % CShape.wordModulus width = _
  exact Nat.mod_eq_of_lt ((Nat.mod_le _ _).trans_lt second.toNat_lt)

/-- Native division followed by rotation is exactly the original total Euclidean step. -/
lemma gcdOperands_divRem_step {width : Nat}
    (first second : CShape.Word width) :
    decodeEuclidState (CShape.divRem width width (.product second first)).second first =
      ClassicalAlgorithms.NumberTheory.Euclid.step
        (decodeEuclidState first second) := by
  unfold decodeEuclidState ClassicalAlgorithms.NumberTheory.Euclid.step
  rw [gcdOperands_divRem_remainder]

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
