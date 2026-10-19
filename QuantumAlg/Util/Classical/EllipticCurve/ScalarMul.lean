/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Classical.EllipticCurve
import all QuantumAlg.Util.Classical.Modular.Additive
/-!
# Fixed-width elliptic-curve scalar multiplication semantics

This module gives total fixed-width natural-scalar semantics over the complete
Mathlib affine-point carrier.  A scalar is an intrinsic `Word scalarWidth`, and
the MSB-first transition visits every declared slot using total point doubling
and addition.  Its final value is the ordinary natural scalar action on the
input point.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace EllipticCurve
namespace ScalarMul

noncomputable section

/-- A complete point together with an intrinsically bounded scalar width. -/
structure Input {width : Nat} (spec : CurveSpec width) (scalarWidth : Nat) where
  /-- The natural scalar stored in exactly the declared number of bits. -/
  scalar : Word scalarWidth
  /-- The complete affine point, including the point at infinity. -/
  point : Point spec

/-- Every intrinsic scalar and complete point form a valid input. -/
@[nolint unusedArguments]
def valid {width scalarWidth : Nat} {spec : CurveSpec width}
    (_input : Input spec scalarWidth) : Prop :=
  True

/-- Mathematical acceptance relation for fixed-width scalar multiplication. -/
def accepts {width scalarWidth : Nat} {spec : CurveSpec width}
    (input : Input spec scalarWidth) (output : Point spec) : Prop :=
  output = input.scalar.val • input.point

/-- The bit visited at an MSB-first scalar loop index. -/
def scalarBit {scalarWidth : Nat} (scalar : Word scalarWidth)
    (index : Fin scalarWidth) : Bool :=
  Modular.Pow.exponentBit scalar index

/-- The natural prefix represented by the first processed scalar slots. -/
def scalarPrefix {scalarWidth : Nat} (scalar : Word scalarWidth)
    (processed : Nat) : Nat :=
  Modular.Pow.exponentPrefix scalar processed

/-- No processed scalar slots represent the natural number zero. -/
@[simp] lemma scalarPrefix_zero {scalarWidth : Nat} (scalar : Word scalarWidth) :
    scalarPrefix scalar 0 = 0 :=
  Modular.Pow.modularPow_exponentPrefix_zero scalar

/-- Processing one scalar slot appends precisely its MSB-first bit. -/
lemma scalarPrefix_succ {scalarWidth : Nat} (scalar : Word scalarWidth)
    (index : Fin scalarWidth) :
    Nat.bit (scalarBit scalar index) (scalarPrefix scalar index.val) =
      scalarPrefix scalar (index.val + 1) :=
  Modular.Pow.modularPow_exponentPrefix_succ scalar index

/-- After every declared scalar slot, the prefix is the stored scalar value. -/
@[simp] lemma scalarPrefix_final {scalarWidth : Nat} (scalar : Word scalarWidth) :
    scalarPrefix scalar scalarWidth = scalar.val :=
  Modular.Pow.modularPow_exponentPrefix_final scalar

/-- The all-zero scalar at any declared width. -/
def zeroScalar (scalarWidth : Nat) : Word scalarWidth :=
  ⟨0, Nat.two_pow_pos scalarWidth⟩

@[simp] lemma zeroScalar_val (scalarWidth : Nat) :
    (zeroScalar scalarWidth).val = 0 :=
  rfl

/-- The scalar one in a nonempty fixed-width word. -/
def oneScalar (scalarWidth : Nat) : Word (scalarWidth + 1) :=
  ⟨1, by
    rw [pow_succ]
    have capacityPositive : 0 < 2 ^ scalarWidth :=
      Nat.two_pow_pos scalarWidth
    omega⟩

@[simp] lemma oneScalar_val (scalarWidth : Nat) :
    (oneScalar scalarWidth).val = 1 :=
  rfl

/-- The scalar whose only set bit is a given in-range bit position. -/
def powerOfTwoScalar (scalarWidth : Nat) (index : Fin scalarWidth) :
    Word scalarWidth :=
  ⟨2 ^ index.val,
    Nat.pow_lt_pow_right (by decide : 1 < 2) index.isLt⟩

@[simp] lemma powerOfTwoScalar_val (scalarWidth : Nat) (index : Fin scalarWidth) :
    (powerOfTwoScalar scalarWidth index).val = 2 ^ index.val :=
  rfl

/-- The largest natural scalar represented by a fixed-width word. -/
def maxScalar (scalarWidth : Nat) : Word scalarWidth :=
  ⟨2 ^ scalarWidth - 1, by
    have capacityPositive : 0 < 2 ^ scalarWidth :=
      Nat.two_pow_pos scalarWidth
    omega⟩

@[simp] lemma maxScalar_val (scalarWidth : Nat) :
    (maxScalar scalarWidth).val = 2 ^ scalarWidth - 1 :=
  rfl

/-- Add one leading zero bit without changing the represented scalar. -/
def leadingZeroScalar {scalarWidth : Nat} (scalar : Word scalarWidth) :
    Word (scalarWidth + 1) :=
  Modular.Pow.leadingZeroExponent scalar

@[simp] lemma leadingZeroScalar_val {scalarWidth : Nat} (scalar : Word scalarWidth) :
    (leadingZeroScalar scalar).val = scalar.val :=
  rfl

/-- The point represented after processing an MSB-first scalar prefix. -/
def partialEval {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) (processed : Nat) : Point spec :=
  scalarPrefix input.scalar processed • input.point

/-- One total MSB-first scalar step: double, then conditionally add the base. -/
def msbStep {width : Nat} (spec : CurveSpec width)
    (base accumulator : Point spec) (bit : Bool) : Point spec :=
  let doubled := Double.eval spec accumulator
  if bit = true then
    Add.eval spec doubled base
  else
    doubled

/-- The empty scalar prefix starts at the point at infinity. -/
@[simp] lemma partialEval_zero {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    partialEval spec input 0 = Point.infinity spec := by
  change scalarPrefix input.scalar 0 • input.point = (0 : Point spec)
  rw [scalarPrefix_zero]
  exact zero_nsmul input.point

/-- One binary group step acts on a natural multiple by appending its bit. -/
private lemma msbStep_nsmul {width : Nat} (spec : CurveSpec width)
    (base : Point spec) (accumulatorScalar : Nat) (bit : Bool) :
    msbStep spec base (accumulatorScalar • base) bit =
      Nat.bit bit accumulatorScalar • base := by
  cases bit with
  | false =>
      change accumulatorScalar • base + accumulatorScalar • base =
        (2 * accumulatorScalar) • base
      rw [← two_nsmul, mul_nsmul']
  | true =>
      change accumulatorScalar • base + accumulatorScalar • base + base =
        (2 * accumulatorScalar + 1) • base
      rw [← two_nsmul, add_nsmul, one_nsmul, mul_nsmul']

/-- Each declared scalar slot advances the accumulator by its total group step. -/
lemma msbStep_partialEval {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) (index : Fin scalarWidth) :
    msbStep spec input.point (partialEval spec input index.val)
        (scalarBit input.scalar index) =
      partialEval spec input (index.val + 1) := by
  change msbStep spec input.point
      (scalarPrefix input.scalar index.val • input.point)
      (scalarBit input.scalar index) =
    scalarPrefix input.scalar (index.val + 1) • input.point
  rw [← scalarPrefix_succ input.scalar index]
  exact msbStep_nsmul spec input.point
    (scalarPrefix input.scalar index.val) (scalarBit input.scalar index)

/-- The final prefix acts by the exact stored natural scalar. -/
lemma partialEval_final {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    partialEval spec input scalarWidth = input.scalar.val • input.point := by
  change scalarPrefix input.scalar scalarWidth • input.point =
    input.scalar.val • input.point
  rw [scalarPrefix_final]

/-- Fixed-width scalar multiplication after all declared scalar slots. -/
def eval {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) : Point spec :=
  partialEval spec input scalarWidth

/-- The evaluator is the ordinary natural scalar action, with no reduction. -/
lemma eval_eq_nsmul {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    eval spec input = input.scalar.val • input.point := by
  change partialEval spec input scalarWidth = input.scalar.val • input.point
  exact partialEval_final spec input

@[simp] lemma scalarMul_valid {width scalarWidth : Nat}
    {spec : CurveSpec width} (input : Input spec scalarWidth) :
    valid input :=
  trivial

/-- The evaluator satisfies the fixed-width scalar acceptance relation. -/
lemma eval_accepts {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    accepts input (eval spec input) := by
  change eval spec input = input.scalar.val • input.point
  exact eval_eq_nsmul spec input

/-- Scalar multiplication returns a point with a canonical fixed-width encoding. -/
lemma eval_isValid {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    Point.IsValid spec (eval spec input) :=
  Point.isValid spec _

/-- The canonical code of a scalar-multiplication output is accepted. -/
lemma encode_eval_isValid {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    Code.IsValid spec (encode spec (eval spec input)) :=
  encode_isValid spec _

/-- A scalar whose stored value is zero maps every point to infinity. -/
lemma eval_of_scalar_val_eq_zero {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) (scalarZero : input.scalar.val = 0) :
    eval spec input = Point.infinity spec := by
  rw [eval_eq_nsmul, scalarZero]
  change 0 • input.point = (0 : Point spec)
  exact zero_nsmul input.point

/-- The all-zero fixed-width scalar maps every point to infinity. -/
@[simp] lemma eval_zeroScalar {width scalarWidth : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec
        ({ scalar := zeroScalar scalarWidth, point := point } : Input spec scalarWidth) =
      Point.infinity spec := by
  apply eval_of_scalar_val_eq_zero
  exact zeroScalar_val scalarWidth

/-- The sole zero-width scalar maps every point to infinity. -/
@[simp] lemma eval_width_zero {width : Nat} (spec : CurveSpec width)
    (input : Input spec 0) :
    eval spec input = Point.infinity spec := by
  apply eval_of_scalar_val_eq_zero
  have scalarRange : input.scalar.val < 2 ^ 0 := input.scalar.isLt
  simp only [pow_zero] at scalarRange
  omega

/-- A scalar whose stored value is one returns the input point. -/
lemma eval_of_scalar_val_eq_one {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) (scalarOne : input.scalar.val = 1) :
    eval spec input = input.point := by
  rw [eval_eq_nsmul, scalarOne]
  exact one_nsmul input.point

/-- The explicit nonempty-width scalar one returns the input point. -/
@[simp] lemma eval_oneScalar {width scalarWidth : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec
        ({ scalar := oneScalar scalarWidth, point := point } : Input spec (scalarWidth + 1)) =
      point := by
  apply eval_of_scalar_val_eq_one
  exact oneScalar_val scalarWidth

/-- Leading zero extension preserves the scalar-multiplication result. -/
lemma eval_leadingZero {width scalarWidth : Nat} (spec : CurveSpec width)
    (input : Input spec scalarWidth) :
    eval spec
        ({ scalar := leadingZeroScalar input.scalar, point := input.point } :
          Input spec (scalarWidth + 1)) =
      eval spec input := by
  calc
    eval spec
        ({ scalar := leadingZeroScalar input.scalar, point := input.point } :
          Input spec (scalarWidth + 1)) =
        (leadingZeroScalar input.scalar).val • input.point :=
      eval_eq_nsmul spec _
    _ = input.scalar.val • input.point := by
      rw [leadingZeroScalar_val]
    _ = eval spec input :=
      (eval_eq_nsmul spec input).symm

/-- A scalar with a specified one-bit value acts by the corresponding power of two. -/
lemma eval_of_scalar_val_eq_powerOfTwo {width scalarWidth : Nat}
    (spec : CurveSpec width) (input : Input spec scalarWidth)
    (index : Fin scalarWidth) (scalarPower : input.scalar.val = 2 ^ index.val) :
    eval spec input = 2 ^ index.val • input.point := by
  rw [eval_eq_nsmul, scalarPower]

/-- The explicit one-bit scalar acts by its corresponding power of two. -/
lemma eval_powerOfTwoScalar {width scalarWidth : Nat} (spec : CurveSpec width)
    (point : Point spec) (index : Fin scalarWidth) :
    eval spec
        ({ scalar := powerOfTwoScalar scalarWidth index, point := point } :
          Input spec scalarWidth) =
      2 ^ index.val • point := by
  apply eval_of_scalar_val_eq_powerOfTwo
  exact powerOfTwoScalar_val scalarWidth index

/-- The maximum fixed-width scalar acts by its exact maximal natural value. -/
lemma eval_maxScalar {width scalarWidth : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec
        ({ scalar := maxScalar scalarWidth, point := point } : Input spec scalarWidth) =
      (2 ^ scalarWidth - 1) • point := by
  calc
    eval spec
        ({ scalar := maxScalar scalarWidth, point := point } : Input spec scalarWidth) =
        (maxScalar scalarWidth).val • point :=
      eval_eq_nsmul spec _
    _ = (2 ^ scalarWidth - 1) • point := by
      rw [maxScalar_val]

/-- Scalar multiplication maps infinity to infinity at every scalar width. -/
@[simp] lemma eval_infinity {width scalarWidth : Nat} (spec : CurveSpec width)
    (scalar : Word scalarWidth) :
    eval spec
        ({ scalar := scalar, point := Point.infinity spec } : Input spec scalarWidth) =
      Point.infinity spec := by
  calc
    eval spec
        ({ scalar := scalar, point := Point.infinity spec } : Input spec scalarWidth) =
        scalar.val • Point.infinity spec :=
      eval_eq_nsmul spec _
    _ = Point.infinity spec := by
      change scalar.val • (0 : Point spec) = 0
      exact nsmul_zero _

end

end ScalarMul
end EllipticCurve

end ClassicalAlgorithms
end QuantumAlg

end
