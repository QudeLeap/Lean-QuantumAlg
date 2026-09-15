/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Operand-sensitive integer arithmetic charges

This module gives a quantum-free charge schedule for exact integer arithmetic.
Every event carries the operands that determine its charge; no event accepts a
claimed width or cost.  The schedule is an explicit schoolbook model, not a
statement about the wall-clock behavior or heap allocation of Lean's bigint
runtime.  Execution modules must seal their traces before exposing a total
charge, since an arbitrary list of events is not an execution certificate.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- Binary magnitude width of a signed integer.  Sign handling is a constant
overhead and is therefore kept outside the magnitude bit count. -/
def integerMagnitudeBits (value : Int) : Nat :=
  Nat.size value.natAbs

/-- One exact arithmetic event together with the two operands that determine
its result and bit cost.  Unary representation views such as `Int.natAbs` and
casts between naturals and nonnegative integers are not arithmetic events. -/
inductive ArithmeticEvent where
  /-- Signed integer addition. -/
  | intAdd (left right : Int)
  /-- Signed integer subtraction. -/
  | intSub (left right : Int)
  /-- Signed integer multiplication. -/
  | intMul (left right : Int)
  /-- Signed integer comparison. -/
  | intLe (left right : Int)
  /-- Signed integer equality test. -/
  | intEq (left right : Int)
  /-- Natural-number addition. -/
  | natAdd (left right : Nat)
  /-- Truncated natural-number subtraction. -/
  | natSub (left right : Nat)
  /-- Natural-number multiplication. -/
  | natMul (left right : Nat)
  /-- Natural-number comparison. -/
  | natLe (left right : Nat)
  /-- Strict natural-number comparison. -/
  | natLt (left right : Nat)
  /-- Natural-number equality test. -/
  | natEq (left right : Nat)
  /-- Natural-number remainder. -/
  | natMod (dividend modulus : Nat)
  /-- Natural-number quotient. -/
  | natDiv (dividend divisor : Nat)
  /-- Binary logarithm used to derive a fixed-width schedule. -/
  | natLog2 (value : Nat)
  /-- Fixed-width left shift. -/
  | natShiftLeft (value amount : Nat)
  /-- Nearest-integer division of a signed numerator by a signed denominator. -/
  | roundedDiv (left right : Int)
  deriving DecidableEq, Repr

namespace ArithmeticEvent

/-- Maximum magnitude width of the actual operands carried by an event. -/
def operandWidth : ArithmeticEvent → Nat
  | .intAdd left right | .intSub left right | .intMul left right |
      .intLe left right | .intEq left right | .roundedDiv left right =>
      max (integerMagnitudeBits left) (integerMagnitudeBits right)
  | .natAdd left right | .natSub left right | .natMul left right |
      .natLe left right | .natLt left right | .natEq left right |
      .natMod left right |
      .natDiv left right =>
      max (Nat.size left) (Nat.size right)
  | .natLog2 value => Nat.size value
  | .natShiftLeft value amount =>
      max (Nat.size amount) (Nat.size (value <<< amount))

/-- Explicit charge assigned by the schoolbook schedule.  Addition,
subtraction, and comparison are linear in operand width; multiplication is
quadratic; rounded division, natural division, and natural remainder are
assigned four quadratic passes.  A later execution-specific theorem is
responsible for connecting this schedule to the arithmetic operations that
were actually evaluated. -/
def schoolbookCharge (event : ArithmeticEvent) : Nat :=
  match event with
  | .intAdd _ _ | .intSub _ _ | .intLe _ _ | .intEq _ _ |
      .natAdd _ _ | .natSub _ _ | .natLe _ _ | .natLt _ _ | .natEq _ _ |
      .natLog2 _ | .natShiftLeft _ _ =>
      event.operandWidth + 1
  | .intMul _ _ | .natMul _ _ =>
      (event.operandWidth + 1) ^ 2
  | .roundedDiv _ _ | .natMod _ _ | .natDiv _ _ =>
      4 * (event.operandWidth + 1) ^ 2

/-- Every arithmetic event has positive schoolbook charge. -/
theorem schoolbookCharge_pos (event : ArithmeticEvent) :
    0 < event.schoolbookCharge := by
  cases event <;> simp [schoolbookCharge, operandWidth]

/-- One positive operand-width unit is bounded by its schoolbook square. -/
private theorem widthSucc_le_square (width : Nat) :
    width + 1 ≤ (width + 1) ^ 2 := by
  rw [pow_two]
  exact Nat.le_mul_of_pos_left (width + 1) (Nat.zero_lt_succ width)

/-- One schoolbook square is bounded by four copies of itself. -/
private theorem square_le_four_mul_square (width : Nat) :
    (width + 1) ^ 2 ≤ 4 * (width + 1) ^ 2 :=
  Nat.le_mul_of_pos_left _ (by decide)

/-- One positive operand-width unit is bounded by four schoolbook squares. -/
private theorem widthSucc_le_four_mul_square (width : Nat) :
    width + 1 ≤ 4 * (width + 1) ^ 2 :=
  (widthSucc_le_square width).trans (square_le_four_mul_square width)

/-- Every primitive event is bounded by four schoolbook quadratic passes at
the width of the operands carried by that same event. -/
theorem schoolbookCharge_le_four_sq (event : ArithmeticEvent) :
    event.schoolbookCharge ≤ 4 * (event.operandWidth + 1) ^ 2 := by
  cases event with
  | intAdd left right =>
      exact widthSucc_le_four_mul_square
        (max (integerMagnitudeBits left) (integerMagnitudeBits right))
  | intSub left right =>
      exact widthSucc_le_four_mul_square
        (max (integerMagnitudeBits left) (integerMagnitudeBits right))
  | intMul left right =>
      exact square_le_four_mul_square
        (max (integerMagnitudeBits left) (integerMagnitudeBits right))
  | intLe left right =>
      exact widthSucc_le_four_mul_square
        (max (integerMagnitudeBits left) (integerMagnitudeBits right))
  | intEq left right =>
      exact widthSucc_le_four_mul_square
        (max (integerMagnitudeBits left) (integerMagnitudeBits right))
  | natAdd left right =>
      exact widthSucc_le_four_mul_square (max (Nat.size left) (Nat.size right))
  | natSub left right =>
      exact widthSucc_le_four_mul_square (max (Nat.size left) (Nat.size right))
  | natMul left right =>
      exact square_le_four_mul_square (max (Nat.size left) (Nat.size right))
  | natLe left right =>
      exact widthSucc_le_four_mul_square (max (Nat.size left) (Nat.size right))
  | natLt left right =>
      exact widthSucc_le_four_mul_square (max (Nat.size left) (Nat.size right))
  | natEq left right =>
      exact widthSucc_le_four_mul_square (max (Nat.size left) (Nat.size right))
  | natMod _ _ => rfl
  | natDiv _ _ => rfl
  | natLog2 value =>
      exact widthSucc_le_four_mul_square (Nat.size value)
  | natShiftLeft value amount =>
      exact widthSucc_le_four_mul_square
        (max (Nat.size amount) (Nat.size (value <<< amount)))
  | roundedDiv _ _ => rfl

end ArithmeticEvent

/-- Extensional charge of a list of arithmetic events.  This function does not
certify that its argument came from an execution; sealed execution traces use
it only on their internally generated event projection. -/
def arithmeticEventListCharge (events : List ArithmeticEvent) : Nat :=
  (events.map ArithmeticEvent.schoolbookCharge).sum

/-- Largest operand width present in a list of arithmetic events. -/
def arithmeticEventListMaxOperandWidth (events : List ArithmeticEvent) : Nat :=
  (events.map ArithmeticEvent.operandWidth).foldr max 0

/-- Extensional list charge is additive under concatenation. -/
@[simp]
theorem arithmeticEventListCharge_append
    (left right : List ArithmeticEvent) :
    arithmeticEventListCharge (left ++ right) =
      arithmeticEventListCharge left + arithmeticEventListCharge right := by
  simp [arithmeticEventListCharge]

/-- Extensional list charge distributes over a complete flat map. -/
theorem arithmeticEventListCharge_flatMap {Value : Type}
    (values : List Value) (events : Value → List ArithmeticEvent) :
    arithmeticEventListCharge (values.flatMap events) =
      (values.map fun value =>
        arithmeticEventListCharge (events value)).sum := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [List.flatMap_cons, arithmeticEventListCharge_append, ih]
      rfl

/-- A pointwise bound controls the sum of a mapped natural-valued workload. -/
theorem listSumMap_le_length_mul {Value : Type}
    (values : List Value) (work : Value → Nat) (bound : Nat)
    (hwork : ∀ value ∈ values, work value ≤ bound) :
    (values.map work).sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        work value + (rest.map work).sum ≤
            bound + rest.length * bound :=
          Nat.add_le_add (hwork value (by simp))
            (ih (by
              intro tail htail
              exact hwork tail (by simp [htail])))
        _ = (rest.length + 1) * bound := by ring

/-- Adding one event updates the largest operand width by maximum. -/
@[simp]
theorem arithmeticEventListMaxOperandWidth_cons
    (event : ArithmeticEvent) (events : List ArithmeticEvent) :
    arithmeticEventListMaxOperandWidth (event :: events) =
      max event.operandWidth
        (arithmeticEventListMaxOperandWidth events) := by
  rfl

/-- Concatenating event lists takes the maximum of their operand widths. -/
@[simp]
theorem arithmeticEventListMaxOperandWidth_append
    (left right : List ArithmeticEvent) :
    arithmeticEventListMaxOperandWidth (left ++ right) =
      max (arithmeticEventListMaxOperandWidth left)
        (arithmeticEventListMaxOperandWidth right) := by
  induction left with
  | nil => simp [arithmeticEventListMaxOperandWidth]
  | cons event left ih => simp [ih, Nat.max_assoc]

/-- Every member's operand width is bounded by the list maximum. -/
theorem ArithmeticEvent.operandWidth_le_listMax
    {event : ArithmeticEvent} {events : List ArithmeticEvent}
    (hmem : event ∈ events) :
    event.operandWidth ≤ arithmeticEventListMaxOperandWidth events := by
  induction events with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [arithmeticEventListMaxOperandWidth_cons]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

/-- A pointwise operand-width bound controls the largest width of an event
list. -/
theorem arithmeticEventListMaxOperandWidth_le
    {events : List ArithmeticEvent} {width : Nat}
    (h : ∀ event ∈ events, event.operandWidth ≤ width) :
    arithmeticEventListMaxOperandWidth events ≤ width := by
  induction events with
  | nil => simp [arithmeticEventListMaxOperandWidth]
  | cons event events ih =>
      rw [arithmeticEventListMaxOperandWidth_cons]
      exact max_le (h event (by simp))
        (ih (by
          intro tail htail
          exact h tail (by simp [htail])))

/-- A list charge is bounded by its number of events times the square of its
largest actual operand width. -/
theorem arithmeticEventListCharge_le (events : List ArithmeticEvent) :
    arithmeticEventListCharge events ≤
      4 * events.length *
        (arithmeticEventListMaxOperandWidth events + 1) ^ 2 := by
  induction events with
  | nil => simp [arithmeticEventListCharge]
  | cons event events ih =>
      let width := max event.operandWidth
        (arithmeticEventListMaxOperandWidth events)
      have heventWidth : event.operandWidth ≤ width := by
        exact Nat.le_max_left _ _
      have htailWidth : arithmeticEventListMaxOperandWidth events ≤ width := by
        exact Nat.le_max_right _ _
      have heventSquare :
          (event.operandWidth + 1) ^ 2 ≤ (width + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right heventWidth 1) 2
      have htailSquare :
          (arithmeticEventListMaxOperandWidth events + 1) ^ 2 ≤
            (width + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right htailWidth 1) 2
      have hevent :
          event.schoolbookCharge ≤ 4 * (width + 1) ^ 2 :=
        Nat.le_trans event.schoolbookCharge_le_four_sq
          (Nat.mul_le_mul_left 4 heventSquare)
      have htail :
          arithmeticEventListCharge events ≤
            4 * events.length * (width + 1) ^ 2 :=
        Nat.le_trans ih
          (Nat.mul_le_mul_left (4 * events.length) htailSquare)
      change
        event.schoolbookCharge + arithmeticEventListCharge events ≤
          4 * (events.length + 1) * (width + 1) ^ 2
      calc
        event.schoolbookCharge + arithmeticEventListCharge events ≤
            4 * (width + 1) ^ 2 +
              4 * events.length * (width + 1) ^ 2 :=
          Nat.add_le_add hevent htail
        _ = 4 * (events.length + 1) * (width + 1) ^ 2 := by ring

/-- The binary size of a product is at most the sum of the operand sizes. -/
theorem natSize_mul_le_add (left right : Nat) :
    Nat.size (left * right) ≤ Nat.size left + Nat.size right := by
  rw [Nat.size_le, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt
    (Nat.lt_size_self left) (Nat.lt_size_self right)

/-- The binary size of a sum is at most one more than the larger operand
size. -/
theorem natSize_add_le_max_add_one (left right : Nat) :
    Nat.size (left + right) ≤
      max (Nat.size left) (Nat.size right) + 1 := by
  rw [Nat.size_le, pow_succ]
  have hleft : left < 2 ^ max (Nat.size left) (Nat.size right) :=
    (Nat.lt_size_self left).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hright : right < 2 ^ max (Nat.size left) (Nat.size right) :=
    (Nat.lt_size_self right).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  omega

/-- A deliberately uniform binary-size bound for natural powers, including the
zero exponent. -/
theorem natSize_pow_le_mul_add_one (base exponent : Nat) :
    Nat.size (base ^ exponent) ≤ exponent * Nat.size base + 1 := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [pow_succ]
      calc
        Nat.size (base ^ exponent * base) ≤
            Nat.size (base ^ exponent) + Nat.size base :=
          natSize_mul_le_add _ _
        _ ≤ (exponent * Nat.size base + 1) + Nat.size base :=
          Nat.add_le_add_right ih _
        _ = (exponent + 1) * Nat.size base + 1 := by ring

/-- A unary schoolbook-charge function has a uniform polynomial upper bound in
its public input-size parameter. -/
def HasPolynomialSchoolbookChargeBound (work : Nat → Nat) : Prop :=
  ∃ constant degree, ∀ inputBits,
    work inputBits ≤ constant * (inputBits + 1) ^ degree

end NumberTheory
end QuantumAlg

end
