/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.ModEq
import all QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.Classical.Modular.Basic
import all QuantumAlg.Util.Classical.Modular.Reduce
import all QuantumAlg.Util.Classical.Modular.Multiplicative

/-!
# Canonical fixed-exponent-width modular power

The exponent is an intrinsically bounded `Word exponentWidth`, so its declared
width remains present in the public type even when its numerical value has
leading zero bits.  This pure layer states mathematical power semantics; the
Components realization is responsible for visiting exactly that many slots.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace Modular
namespace Pow

/-- A canonical base and an exponent with an explicit fixed width. -/
structure Input {width : Nat} (spec : ModulusSpec width) (exponentWidth : Nat) where
  /-- The canonical modular base. -/
  base : Residue spec
  /-- The fixed-width exponent, including any leading zero bits. -/
  exponent : Word exponentWidth
deriving DecidableEq

/-- Every intrinsic base and fixed-width exponent form a valid power input. -/
@[nolint unusedArguments]
def valid {width exponentWidth : Nat} {spec : ModulusSpec width}
    (_input : Input spec exponentWidth) : Prop :=
  True

/-- Mathematical acceptance relation for modular exponentiation. -/
def accepts {width exponentWidth : Nat} {spec : ModulusSpec width}
    (input : Input spec exponentWidth) (output : Residue spec) : Prop :=
  output.val = input.base.val ^ input.exponent.val % spec.modulus

/-- Canonical fixed-width modular exponentiation semantics. -/
def eval {width exponentWidth : Nat} (spec : ModulusSpec width)
    (input : Input spec exponentWidth) : Residue spec :=
  Residue.ofNat spec (input.base.val ^ input.exponent.val)

/-- The exponent bit visited at an MSB-first loop index. -/
def exponentBit {exponentWidth : Nat} (exponent : Word exponentWidth)
    (index : Fin exponentWidth) : Bool :=
  exponent.val.testBit (exponentWidth - 1 - index.val)

/-- The numeric prefix represented by the first `processed` exponent slots. -/
def exponentPrefix {exponentWidth : Nat} (exponent : Word exponentWidth)
    (processed : Nat) : Nat :=
  exponent.val >>> (exponentWidth - processed)

/-- Mathematical accumulator after processing an MSB-first exponent prefix. -/
def partialEval {width exponentWidth : Nat} (spec : ModulusSpec width)
    (input : Input spec exponentWidth) (processed : Nat) : Residue spec :=
  Residue.ofNat spec
    (input.base.val ^ exponentPrefix input.exponent processed)

/-- One left-to-right binary exponentiation step. -/
def msbStep {width : Nat} (spec : ModulusSpec width)
    (base accumulator : Residue spec) (bit : Bool) : Residue spec :=
  let squared := Square.eval spec accumulator
  if bit = true then
    Mul.eval spec { left := squared, right := base }
  else
    squared

/-- No exponent slots processed means that the represented prefix is zero. -/
@[simp] theorem modularPow_exponentPrefix_zero {exponentWidth : Nat}
    (exponent : Word exponentWidth) :
    exponentPrefix exponent 0 = 0 := by
  rw [exponentPrefix]
  simp only [Nat.sub_zero, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt exponent.isLt

/-- Processing one more slot appends its bit to the represented prefix. -/
theorem modularPow_exponentPrefix_succ {exponentWidth : Nat}
    (exponent : Word exponentWidth) (index : Fin exponentWidth) :
    Nat.bit (exponentBit exponent index)
        (exponentPrefix exponent index.val) =
      exponentPrefix exponent (index.val + 1) := by
  have indexRange : index.val < exponentWidth := index.isLt
  have currentExponent :
      exponentWidth - index.val =
        (exponentWidth - 1 - index.val) + 1 := by
    omega
  have nextExponent :
      exponentWidth - (index.val + 1) =
        exponentWidth - 1 - index.val := by
    omega
  have currentShift :
      exponent.val >>> ((exponentWidth - 1 - index.val) + 1) =
        (exponent.val >>> (exponentWidth - 1 - index.val)) >>> 1 :=
    Nat.shiftRight_add exponent.val
      (exponentWidth - 1 - index.val) 1
  have currentBit :
      exponent.val.testBit (exponentWidth - 1 - index.val) =
        (exponent.val >>> (exponentWidth - 1 - index.val)).testBit 0 := by
    simpa only [Nat.add_zero] using
      (Nat.testBit_shiftRight (x := exponent.val)
        (i := exponentWidth - 1 - index.val) (j := 0)).symm
  rw [exponentPrefix, exponentPrefix, exponentBit,
    currentExponent, nextExponent]
  rw [currentShift, currentBit]
  exact Nat.bit_testBit_zero_shiftRight_one
    (exponent.val >>> (exponentWidth - 1 - index.val))

/-- After every declared slot, the represented prefix is the full exponent. -/
@[simp] theorem modularPow_exponentPrefix_final {exponentWidth : Nat}
    (exponent : Word exponentWidth) :
    exponentPrefix exponent exponentWidth = exponent.val := by
  simp [exponentPrefix]

/-- The empty exponent prefix initializes the accumulator to canonical one. -/
@[simp] theorem modularPow_partialEval_zero {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    partialEval spec input 0 = Residue.one spec := by
  simp [partialEval, Residue.one]

/-- The accumulator after all slots agrees with the public power semantics. -/
@[simp] theorem modularPow_partialEval_final {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    partialEval spec input exponentWidth = eval spec input := by
  simp [partialEval, eval]

/-- One MSB step advances the semantic accumulator by exactly one slot. -/
theorem modularPow_msbStep_partialEval {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth)
    (index : Fin exponentWidth) :
    msbStep spec input.base (partialEval spec input index.val)
        (exponentBit input.exponent index) =
      partialEval spec input (index.val + 1) := by
  have accumulatorEquivalent :
      (partialEval spec input index.val).val ≡
        input.base.val ^ exponentPrefix input.exponent index.val
        [MOD spec.modulus] :=
    Residue.residueOfNat_modEq spec
      (input.base.val ^ exponentPrefix input.exponent index.val)
  have squaredEquivalent :
      (Square.eval spec (partialEval spec input index.val)).val ≡
        input.base.val ^
          (2 * exponentPrefix input.exponent index.val)
        [MOD spec.modulus] := by
    calc
      (Square.eval spec (partialEval spec input index.val)).val ≡
          (partialEval spec input index.val).val *
            (partialEval spec input index.val).val [MOD spec.modulus] :=
        Square.modularSquare_eval_modEq spec
          (partialEval spec input index.val)
      _ ≡
          input.base.val ^ exponentPrefix input.exponent index.val *
            input.base.val ^ exponentPrefix input.exponent index.val
          [MOD spec.modulus] :=
        accumulatorEquivalent.mul accumulatorEquivalent
      _ = input.base.val ^
          (2 * exponentPrefix input.exponent index.val) := by
        rw [two_mul, pow_add]
  have stepEquivalent :
      (msbStep spec input.base (partialEval spec input index.val)
          (exponentBit input.exponent index)).val ≡
        input.base.val ^
          Nat.bit (exponentBit input.exponent index)
            (exponentPrefix input.exponent index.val)
        [MOD spec.modulus] := by
    by_cases bitSet : exponentBit input.exponent index = true
    · simp only [msbStep, if_pos bitSet]
      calc
        (Mul.eval spec
            { left := Square.eval spec (partialEval spec input index.val)
              right := input.base }).val ≡
            (Square.eval spec (partialEval spec input index.val)).val *
              input.base.val [MOD spec.modulus] :=
          Mul.modularMul_eval_modEq spec
            { left := Square.eval spec (partialEval spec input index.val)
              right := input.base }
        _ ≡
            input.base.val ^
                  (2 * exponentPrefix input.exponent index.val) *
              input.base.val [MOD spec.modulus] :=
          squaredEquivalent.mul (Nat.ModEq.refl input.base.val)
        _ = input.base.val ^
            Nat.bit (exponentBit input.exponent index)
              (exponentPrefix input.exponent index.val) := by
          rw [bitSet, Nat.bit_true_apply, pow_succ]
    · have bitClear : exponentBit input.exponent index = false :=
        Bool.eq_false_of_not_eq_true bitSet
      simp only [msbStep, if_neg bitSet]
      simpa only [bitClear, Nat.bit_false_apply] using squaredEquivalent
  have stepAtNextPrefix :
      (msbStep spec input.base (partialEval spec input index.val)
          (exponentBit input.exponent index)).val ≡
        input.base.val ^
          exponentPrefix input.exponent (index.val + 1)
        [MOD spec.modulus] := by
    rw [← modularPow_exponentPrefix_succ input.exponent index]
    exact stepEquivalent
  have targetEquivalent :
      (partialEval spec input (index.val + 1)).val ≡
        input.base.val ^
          exponentPrefix input.exponent (index.val + 1)
        [MOD spec.modulus] :=
    Residue.residueOfNat_modEq spec
      (input.base.val ^
        exponentPrefix input.exponent (index.val + 1))
  apply Fin.ext
  exact (stepAtNextPrefix.trans targetEquivalent.symm).eq_of_lt_of_lt
    (msbStep spec input.base (partialEval spec input index.val)
      (exponentBit input.exponent index)).isLt
    (partialEval spec input (index.val + 1)).isLt

@[simp] theorem modularPow_valid {width exponentWidth : Nat}
    {spec : ModulusSpec width} (input : Input spec exponentWidth) :
    valid input :=
  trivial

@[simp] theorem modularPow_eval_val {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    (eval spec input).val =
      input.base.val ^ input.exponent.val % spec.modulus :=
  rfl

theorem modularPow_eval_range {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

theorem modularPow_eval_modEq {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    (eval spec input).val ≡
      input.base.val ^ input.exponent.val [MOD spec.modulus] :=
  Residue.residueOfNat_modEq spec (input.base.val ^ input.exponent.val)

theorem modularPow_eval_accepts {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    accepts input (eval spec input) :=
  rfl

/-- Increasing an exponent's width by one can preserve its exact value. -/
theorem modularPow_exponent_lt_extended {exponentWidth : Nat}
    (exponent : Word exponentWidth) :
    exponent.val < ClassicalAlgorithms.modulus (exponentWidth + 1) := by
  have capacityPositive := ClassicalAlgorithms.fixedWidthModulus_pos exponentWidth
  have exponentRange := ClassicalAlgorithms.fixedWidthWord_lt_modulus exponent
  simp only [ClassicalAlgorithms.modulus, pow_succ] at capacityPositive exponentRange ⊢
  omega

/-- Add one leading zero bit without changing the represented exponent. -/
def leadingZeroExponent {exponentWidth : Nat} (exponent : Word exponentWidth) :
    Word (exponentWidth + 1) :=
  ⟨exponent.val, modularPow_exponent_lt_extended exponent⟩

@[simp] theorem modularPow_leadingZeroExponent_val {exponentWidth : Nat}
    (exponent : Word exponentWidth) :
    (leadingZeroExponent exponent).val = exponent.val :=
  rfl

/-- A leading zero changes the declared work width but not mathematical power. -/
theorem modularPow_eval_leadingZero {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth) :
    eval spec
        ({ base := input.base
           exponent := leadingZeroExponent input.exponent } :
          Input spec (exponentWidth + 1)) =
      eval spec input := by
  apply Fin.ext
  simp

/-- Exponent zero returns canonical one modulo every admitted modulus. -/
theorem modularPow_eval_exponent_zero {width exponentWidth : Nat}
    (spec : ModulusSpec width) (input : Input spec exponentWidth)
    (exponentZero : input.exponent.val = 0) :
    eval spec input = Residue.one spec := by
  apply Fin.ext
  simp [exponentZero, Nat.mod_eq_of_lt (modulusSpec_one_lt spec)]

/-- The unique zero-width exponent is zero and therefore returns one. -/
@[simp] theorem modularPow_eval_width_zero {width : Nat}
    (spec : ModulusSpec width) (input : Input spec 0) :
    eval spec input = Residue.one spec := by
  have exponentRange := ClassicalAlgorithms.fixedWidthWord_lt_modulus input.exponent
  simp only [ClassicalAlgorithms.modulus, pow_zero] at exponentRange
  have exponentZero : input.exponent.val = 0 := by
    omega
  exact modularPow_eval_exponent_zero spec input exponentZero

/-- Canonical one raised to any fixed-width exponent remains one. -/
@[simp] theorem modularPow_eval_base_one {width exponentWidth : Nat}
    (spec : ModulusSpec width) (exponent : Word exponentWidth) :
    eval spec { base := Residue.one spec, exponent := exponent } =
      Residue.one spec := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt (modulusSpec_one_lt spec)]

/-- Canonical zero raised to a nonzero exponent remains zero. -/
theorem modularPow_eval_base_zero_of_exponent_ne_zero
    {width exponentWidth : Nat} (spec : ModulusSpec width)
    (exponent : Word exponentWidth) (exponentNonzero : exponent.val ≠ 0) :
    eval spec { base := Residue.zero spec, exponent := exponent } =
      Residue.zero spec := by
  apply Fin.ext
  simp [exponentNonzero]

end Pow
end Modular

end ClassicalAlgorithms
end QuantumAlg

end
