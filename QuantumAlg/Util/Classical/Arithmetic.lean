/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Pure fixed-width classical arithmetic

This quantum-free module defines the mathematical input and output carriers for
four reusable fixed-width arithmetic operations.  Words reuse
`Nat.FixedWidth.Word`; their bounds therefore belong to the type rather than to
an external size claim.

Addition and subtraction return their low word together with the corresponding
carry or borrow bit.  Full multiplication uses the sum of the operand widths.
Division and remainder have a proof-carrying public evaluator, so a zero divisor
cannot be treated as a valid result merely because natural-number division is
total in Lean.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms


/-- The shared intrinsic carrier for an unsigned fixed-width word. -/
public abbrev Word (width : Nat) := Nat.FixedWidth.Word width

/-- The positive natural modulus represented by one word width. -/
@[expose] public def modulus (width : Nat) : Nat :=
  2 ^ width

theorem fixedWidthModulus_pos (width : Nat) : 0 < modulus width := by
  exact Nat.two_pow_pos width

/-- Canonically truncate a natural number to one fixed-width word. -/
def wordOfNat (width value : Nat) : Word width :=
  ⟨value % modulus width, Nat.mod_lt value (fixedWidthModulus_pos width)⟩

@[simp] theorem fixedWidthWordOfNat_val (width value : Nat) :
    (wordOfNat width value).val = value % modulus width :=
  rfl

/-- Every word value is in the exact range determined by its width. -/
theorem fixedWidthWord_lt_modulus {width : Nat} (word : Word width) :
    word.val < modulus width := by
  unfold modulus
  exact word.isLt

namespace AddCarry

/-- Two equal-width operands for addition with carry. -/
structure Input (width : Nat) where
  /-- The left addend. -/
  left : Word width
  /-- The right addend. -/
  right : Word width
deriving DecidableEq

/-- The low word and the single carry-out bit. -/
structure Output (width : Nat) where
  /-- The low `width` bits of the sum. -/
  low : Word width
  /-- Whether the mathematical sum exceeds the output word. -/
  carry : Bool
deriving DecidableEq

/-- Every intrinsically bounded input is valid for addition. -/
@[nolint unusedArguments]
def valid {width : Nat} (_input : Input width) : Prop :=
  True

/-- Mathematical acceptance relation for addition with carry. -/
def accepts {width : Nat} (input : Input width) (output : Output width) : Prop :=
  output.low.val + output.carry.toNat * modulus width =
      input.left.val + input.right.val ∧
    output.carry =
      decide (modulus width ≤ input.left.val + input.right.val)

/-- Pure fixed-width addition with an explicit carry-out bit. -/
def eval {width : Nat} (input : Input width) : Output width where
  low := wordOfNat width (input.left.val + input.right.val)
  carry := decide (modulus width ≤ input.left.val + input.right.val)

theorem addCarry_input_range {width : Nat} (input : Input width) :
    input.left.val < modulus width ∧ input.right.val < modulus width :=
  ⟨fixedWidthWord_lt_modulus input.left,
    fixedWidthWord_lt_modulus input.right⟩

@[simp] theorem addCarry_valid {width : Nat} (input : Input width) :
    valid input :=
  trivial

/-- The mathematical sum fits in one additional bit. -/
theorem addCarry_sum_lt_double {width : Nat} (input : Input width) :
    input.left.val + input.right.val < 2 * modulus width := by
  rcases addCarry_input_range input with ⟨leftRange, rightRange⟩
  omega

theorem addCarry_sum_lt_next_modulus {width : Nat} (input : Input width) :
    input.left.val + input.right.val < modulus (width + 1) := by
  simpa [modulus, pow_succ, Nat.mul_comm] using
    addCarry_sum_lt_double input

@[simp] theorem addCarry_eval_low {width : Nat} (input : Input width) :
    (eval input).low.val =
      (input.left.val + input.right.val) % modulus width :=
  rfl

@[simp] theorem addCarry_eval_carry {width : Nat} (input : Input width) :
    (eval input).carry =
      decide (modulus width ≤ input.left.val + input.right.val) :=
  rfl

theorem addCarry_eval_low_range {width : Nat} (input : Input width) :
    (eval input).low.val < modulus width :=
  fixedWidthWord_lt_modulus (eval input).low

theorem addCarry_eval_carry_eq_true_iff {width : Nat} (input : Input width) :
    (eval input).carry = true ↔
      modulus width ≤ input.left.val + input.right.val := by
  simp [eval]

/-- The low word and carry bit reconstruct the unbounded mathematical sum. -/
theorem addCarry_eval_reconstruct {width : Nat} (input : Input width) :
    (eval input).low.val + (eval input).carry.toNat * modulus width =
      input.left.val + input.right.val := by
  change
    (input.left.val + input.right.val) % modulus width +
        (decide (modulus width ≤ input.left.val + input.right.val)).toNat *
          modulus width =
      input.left.val + input.right.val
  by_cases carry : modulus width ≤ input.left.val + input.right.val
  · have lowRange :
        input.left.val + input.right.val - modulus width < modulus width := by
      have sumRange := addCarry_sum_lt_double input
      omega
    rw [Nat.mod_eq_sub_mod carry, Nat.mod_eq_of_lt lowRange]
    simp [carry, Nat.sub_add_cancel carry]
  · have sumRange :
        input.left.val + input.right.val < modulus width :=
      Nat.lt_of_not_ge carry
    rw [Nat.mod_eq_of_lt sumRange]
    simp [carry]

theorem addCarry_eval_accepts {width : Nat} (input : Input width) :
    accepts input (eval input) :=
  ⟨addCarry_eval_reconstruct input, addCarry_eval_carry input⟩

end AddCarry

namespace SubBorrow

/-- Two equal-width operands for subtraction with borrow. -/
structure Input (width : Nat) where
  /-- The minuend. -/
  left : Word width
  /-- The subtrahend. -/
  right : Word width
deriving DecidableEq

/-- The wrapped low word and the single borrow-out bit. -/
structure Output (width : Nat) where
  /-- The low `width` bits of the wrapped difference. -/
  low : Word width
  /-- Whether the subtraction borrows one modulus. -/
  borrow : Bool
deriving DecidableEq

@[ext] theorem Output.ext {width : Nat} {left right : Output width}
    (low : left.low = right.low) (borrow : left.borrow = right.borrow) :
    left = right := by
  cases left
  cases right
  cases low
  cases borrow
  rfl

/-- Every intrinsically bounded input is valid for subtraction. -/
@[nolint unusedArguments]
def valid {width : Nat} (_input : Input width) : Prop :=
  True

/-- Mathematical acceptance relation for subtraction with borrow. -/
def accepts {width : Nat} (input : Input width) (output : Output width) : Prop :=
  input.left.val + output.borrow.toNat * modulus width =
      input.right.val + output.low.val ∧
    output.borrow = decide (input.left.val < input.right.val)

/-- The canonical natural representative of the wrapped difference. -/
def difference {width : Nat} (input : Input width) : Nat :=
  if input.left.val < input.right.val then
    input.left.val + modulus width - input.right.val
  else
    input.left.val - input.right.val

/-- Pure fixed-width subtraction with an explicit borrow-out bit. -/
def eval {width : Nat} (input : Input width) : Output width where
  low := wordOfNat width (difference input)
  borrow := decide (input.left.val < input.right.val)

theorem subBorrow_input_range {width : Nat} (input : Input width) :
    input.left.val < modulus width ∧ input.right.val < modulus width :=
  ⟨fixedWidthWord_lt_modulus input.left,
    fixedWidthWord_lt_modulus input.right⟩

@[simp] theorem subBorrow_valid {width : Nat} (input : Input width) :
    valid input :=
  trivial

/-- The selected wrapped-difference representative is itself in range. -/
theorem subBorrow_difference_lt {width : Nat} (input : Input width) :
    difference input < modulus width := by
  rcases subBorrow_input_range input with ⟨leftRange, rightRange⟩
  have modulusPositive := fixedWidthModulus_pos width
  by_cases borrow : input.left.val < input.right.val
  · simp only [difference, if_pos borrow]
    omega
  · have rightLeLeft : input.right.val ≤ input.left.val :=
      Nat.le_of_not_gt borrow
    simp only [difference, if_neg borrow]
    omega

@[simp] theorem subBorrow_eval_low {width : Nat} (input : Input width) :
    (eval input).low.val = difference input := by
  change difference input % modulus width = difference input
  exact Nat.mod_eq_of_lt (subBorrow_difference_lt input)

@[simp] theorem subBorrow_eval_borrow {width : Nat} (input : Input width) :
    (eval input).borrow = decide (input.left.val < input.right.val) :=
  rfl

theorem subBorrow_eval_low_range {width : Nat} (input : Input width) :
    (eval input).low.val < modulus width :=
  fixedWidthWord_lt_modulus (eval input).low

theorem subBorrow_eval_borrow_eq_true_iff {width : Nat} (input : Input width) :
    (eval input).borrow = true ↔ input.left.val < input.right.val := by
  simp [eval]

/-- The branch form agrees with ordinary fixed-width modular subtraction. -/
theorem subBorrow_eval_low_eq_wrapping {width : Nat} (input : Input width) :
    (eval input).low.val =
      (input.left.val + modulus width - input.right.val) % modulus width := by
  rw [subBorrow_eval_low]
  rcases subBorrow_input_range input with ⟨leftRange, rightRange⟩
  have modulusPositive := fixedWidthModulus_pos width
  by_cases borrow : input.left.val < input.right.val
  · have wrappedRange :
        input.left.val + modulus width - input.right.val < modulus width := by
      omega
    simp [difference, borrow, Nat.mod_eq_of_lt wrappedRange]
  · have rightLeLeft : input.right.val ≤ input.left.val :=
      Nat.le_of_not_gt borrow
    have differenceRange :
        input.left.val - input.right.val < modulus width := by
      omega
    have split :
        input.left.val + modulus width - input.right.val =
          (input.left.val - input.right.val) + modulus width := by
      omega
    simp only [difference, if_neg borrow]
    rw [split]
    simp [Nat.mod_eq_of_lt differenceRange]

/-- The low word and borrow bit reconstruct the mathematical subtraction. -/
theorem subBorrow_eval_reconstruct {width : Nat} (input : Input width) :
    input.left.val + (eval input).borrow.toNat * modulus width =
      input.right.val + (eval input).low.val := by
  by_cases borrow : input.left.val < input.right.val
  · have rightLeAugmented :
        input.right.val ≤ input.left.val + modulus width := by
      have rightRange := fixedWidthWord_lt_modulus input.right
      have modulusPositive := fixedWidthModulus_pos width
      omega
    calc
      input.left.val + (eval input).borrow.toNat * modulus width =
          input.left.val + modulus width := by
            rw [subBorrow_eval_borrow]
            simp [borrow]
      _ = input.right.val +
          (input.left.val + modulus width - input.right.val) :=
        (Nat.add_sub_of_le rightLeAugmented).symm
      _ = input.right.val + (eval input).low.val := by
        rw [subBorrow_eval_low]
        simp [difference, borrow]
  · have rightLeLeft : input.right.val ≤ input.left.val :=
      Nat.le_of_not_gt borrow
    calc
      input.left.val + (eval input).borrow.toNat * modulus width =
          input.left.val := by
            rw [subBorrow_eval_borrow]
            simp [borrow]
      _ = input.right.val + (input.left.val - input.right.val) :=
        (Nat.add_sub_of_le rightLeLeft).symm
      _ = input.right.val + (eval input).low.val := by
        rw [subBorrow_eval_low]
        simp [difference, borrow]

theorem subBorrow_eval_accepts {width : Nat} (input : Input width) :
    accepts input (eval input) :=
  ⟨subBorrow_eval_reconstruct input, subBorrow_eval_borrow input⟩

end SubBorrow

namespace MulFull

/-- Independently sized operands for full-width multiplication. -/
structure Input (leftWidth rightWidth : Nat) where
  /-- The left factor. -/
  left : Word leftWidth
  /-- The right factor. -/
  right : Word rightWidth
deriving DecidableEq

/-- The exact product in the combined operand width. -/
structure Output (leftWidth rightWidth : Nat) where
  /-- The full, untruncated product. -/
  value : Word (leftWidth + rightWidth)
deriving DecidableEq

/-- Every intrinsically bounded input is valid for multiplication. -/
@[nolint unusedArguments]
def valid {leftWidth rightWidth : Nat}
    (_input : Input leftWidth rightWidth) : Prop :=
  True

/-- Mathematical acceptance relation for full-width multiplication. -/
def accepts {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth)
    (output : Output leftWidth rightWidth) : Prop :=
  output.value.val = input.left.val * input.right.val

/-- Pure multiplication into the full combined operand width. -/
def eval {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) : Output leftWidth rightWidth where
  value := wordOfNat (leftWidth + rightWidth)
    (input.left.val * input.right.val)

theorem mulFull_input_range {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) :
    input.left.val < modulus leftWidth ∧
      input.right.val < modulus rightWidth :=
  ⟨fixedWidthWord_lt_modulus input.left,
    fixedWidthWord_lt_modulus input.right⟩

@[simp] theorem mulFull_valid {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) : valid input :=
  trivial

/-- The combined output width is large enough for the exact product. -/
theorem mulFull_math_product_lt {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) :
    input.left.val * input.right.val < modulus (leftWidth + rightWidth) := by
  rw [modulus, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt input.left.isLt input.right.isLt

@[simp] theorem mulFull_eval_value {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) :
    (eval input).value.val = input.left.val * input.right.val := by
  change
    (input.left.val * input.right.val) % modulus (leftWidth + rightWidth) =
      input.left.val * input.right.val
  exact Nat.mod_eq_of_lt (mulFull_math_product_lt input)

theorem mulFull_eval_range {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) :
    (eval input).value.val < modulus (leftWidth + rightWidth) :=
  fixedWidthWord_lt_modulus (eval input).value

theorem mulFull_eval_accepts {leftWidth rightWidth : Nat}
    (input : Input leftWidth rightWidth) : accepts input (eval input) :=
  mulFull_eval_value input

end MulFull

namespace DivRem

/-- A numerator word and an independently sized divisor word. -/
structure Input (numeratorWidth divisorWidth : Nat) where
  /-- The dividend. -/
  numerator : Word numeratorWidth
  /-- The divisor, which the public validity predicate requires to be nonzero. -/
  divisor : Word divisorWidth
deriving DecidableEq

/-- Quotient and remainder in their respective input widths. -/
structure Output (numeratorWidth divisorWidth : Nat) where
  /-- The quotient in the numerator width. -/
  quotient : Word numeratorWidth
  /-- The remainder in the divisor width. -/
  remainder : Word divisorWidth
deriving DecidableEq

/-- Public division is valid exactly when the represented divisor is nonzero. -/
def valid {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) : Prop :=
  input.divisor.val ≠ 0

instance {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) : Decidable (valid input) := by
  unfold valid
  infer_instance

/-- Standard quotient/remainder acceptance, including the public validity gate. -/
def accepts {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth)
    (output : Output numeratorWidth divisorWidth) : Prop :=
  valid input ∧
    output.quotient.val * input.divisor.val + output.remainder.val =
      input.numerator.val ∧
    output.remainder.val < input.divisor.val

instance {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth)
    (output : Output numeratorWidth divisorWidth) : Decidable (accepts input output) := by
  unfold accepts
  infer_instance

/-- Proof-carrying public division and remainder evaluation.

The validity proof is an input to the evaluator even though the quotient and
remainder formulas do not inspect proof data.  Consequently there is no public
evaluation term for a zero divisor. -/
@[nolint unusedArguments]
def eval {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (_valid : valid input) :
    Output numeratorWidth divisorWidth where
  quotient := wordOfNat numeratorWidth
    (input.numerator.val / input.divisor.val)
  remainder := wordOfNat divisorWidth
    (input.numerator.val % input.divisor.val)

theorem divRem_input_range {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) :
    input.numerator.val < modulus numeratorWidth ∧
      input.divisor.val < modulus divisorWidth :=
  ⟨fixedWidthWord_lt_modulus input.numerator,
    fixedWidthWord_lt_modulus input.divisor⟩

theorem divRem_valid_iff {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) :
    valid input ↔ input.divisor.val ≠ 0 :=
  Iff.rfl

theorem divRem_divisor_pos {numeratorWidth divisorWidth : Nat}
    {input : Input numeratorWidth divisorWidth} (inputValid : valid input) :
    0 < input.divisor.val :=
  Nat.pos_of_ne_zero inputValid

theorem divRem_zero_divisor_not_valid {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth)
    (divisorZero : input.divisor.val = 0) : ¬ valid input := by
  simp [valid, divisorZero]

theorem divRem_zero_divisor_not_accepted {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth)
    (divisorZero : input.divisor.val = 0)
    (output : Output numeratorWidth divisorWidth) : ¬ accepts input output := by
  intro accepted
  exact (divRem_zero_divisor_not_valid input divisorZero) accepted.1

@[simp] theorem divRem_eval_quotient {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (inputValid : valid input) :
    (eval input inputValid).quotient.val =
      input.numerator.val / input.divisor.val := by
  change
    (input.numerator.val / input.divisor.val) % modulus numeratorWidth =
      input.numerator.val / input.divisor.val
  exact Nat.mod_eq_of_lt
    ((Nat.div_le_self input.numerator.val input.divisor.val).trans_lt
      (fixedWidthWord_lt_modulus input.numerator))

@[simp] theorem divRem_eval_remainder {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (inputValid : valid input) :
    (eval input inputValid).remainder.val =
      input.numerator.val % input.divisor.val := by
  change
    (input.numerator.val % input.divisor.val) % modulus divisorWidth =
      input.numerator.val % input.divisor.val
  exact Nat.mod_eq_of_lt
    ((Nat.mod_lt input.numerator.val (divRem_divisor_pos inputValid)).trans
      (fixedWidthWord_lt_modulus input.divisor))

theorem divRem_eval_output_range {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (inputValid : valid input) :
    (eval input inputValid).quotient.val < modulus numeratorWidth ∧
      (eval input inputValid).remainder.val < modulus divisorWidth :=
  ⟨fixedWidthWord_lt_modulus (eval input inputValid).quotient,
    fixedWidthWord_lt_modulus (eval input inputValid).remainder⟩

/-- Valid quotient and remainder reconstruct the numerator exactly. -/
theorem divRem_eval_reconstruct {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (inputValid : valid input) :
    (eval input inputValid).quotient.val * input.divisor.val +
        (eval input inputValid).remainder.val = input.numerator.val := by
  rw [divRem_eval_quotient, divRem_eval_remainder]
  simpa [Nat.mul_comm] using
    Nat.div_add_mod input.numerator.val input.divisor.val

theorem divRem_eval_remainder_lt {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (inputValid : valid input) :
    (eval input inputValid).remainder.val < input.divisor.val := by
  rw [divRem_eval_remainder]
  exact Nat.mod_lt input.numerator.val (divRem_divisor_pos inputValid)

theorem divRem_eval_accepts {numeratorWidth divisorWidth : Nat}
    (input : Input numeratorWidth divisorWidth) (inputValid : valid input) :
    accepts input (eval input inputValid) :=
  ⟨inputValid, divRem_eval_reconstruct input inputValid,
    divRem_eval_remainder_lt input inputValid⟩

end DivRem


end ClassicalAlgorithms
end QuantumAlg

end
