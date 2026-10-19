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
import all QuantumAlg.Util.Classical.Modular.Pow

/-!
# Canonical additive modular arithmetic

This module defines pure modular addition, subtraction, negation, and doubling.
Every result uses the same intrinsic canonical-residue carrier as its operands.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace Modular

namespace Add

/-- Two canonical residues to add. -/
structure Input {width : Nat} (spec : ModulusSpec width) where
  /-- The left addend. -/
  left : Residue spec
  /-- The right addend. -/
  right : Residue spec
deriving DecidableEq

/-- Every pair of intrinsic residues is a valid modular-addition input. -/
@[nolint unusedArguments]
def valid {width : Nat} {spec : ModulusSpec width} (_input : Input spec) : Prop :=
  True

/-- Mathematical acceptance relation for modular addition. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Residue spec) : Prop :=
  output.val = (input.left.val + input.right.val) % spec.modulus

/-- The unreduced sum fits exactly in one additional bit. -/
lemma modularAdd_sum_lt_extended {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    input.left.val + input.right.val < ClassicalAlgorithms.modulus (width + 1) := by
  have capacityPositive := ClassicalAlgorithms.fixedWidthModulus_pos width
  have modulusBound := spec.le_capacity
  have leftRange := input.left.isLt
  have rightRange := input.right.isLt
  simp only [ClassicalAlgorithms.modulus, pow_succ] at capacityPositive modulusBound ⊢
  omega

/-- The exact unreduced sum represented in one additional bit. -/
def sumWord {width : Nat} {spec : ModulusSpec width} (input : Input spec) :
    Word (width + 1) :=
  ⟨input.left.val + input.right.val, modularAdd_sum_lt_extended input⟩

@[simp] lemma modularAdd_sumWord_val {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    (sumWord input).val = input.left.val + input.right.val :=
  rfl

/-- Canonical modular addition, expressed as reduction of the exact widened sum. -/
def eval {width : Nat} (spec : ModulusSpec width) (input : Input spec) :
    Residue spec :=
  Reduce.eval spec (sumWord input)

@[simp] lemma modularAdd_valid {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    valid input :=
  trivial

lemma modularAdd_eval_eq_reduce {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = Reduce.eval spec (sumWord input) :=
  rfl

@[simp] lemma modularAdd_eval_val {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val =
      (input.left.val + input.right.val) % spec.modulus :=
  rfl

lemma modularAdd_eval_range {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

lemma modularAdd_eval_modEq {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val ≡
      input.left.val + input.right.val [MOD spec.modulus] := by
  simpa only [modularAdd_eval_eq_reduce, modularAdd_sumWord_val] using
    Reduce.modularReduce_eval_modEq spec (sumWord input)

lemma modularAdd_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    accepts input (eval spec input) :=
  rfl

lemma modularAdd_eval_val_of_sum_lt {width : Nat} (spec : ModulusSpec width)
    (input : Input spec)
    (sumRange : input.left.val + input.right.val < spec.modulus) :
    (eval spec input).val = input.left.val + input.right.val := by
  rw [modularAdd_eval_val, Nat.mod_eq_of_lt sumRange]

/-- When addition crosses the modulus once, evaluation performs exact wraparound. -/
lemma modularAdd_eval_val_of_modulus_le {width : Nat}
    (spec : ModulusSpec width) (input : Input spec)
    (modulusLe : spec.modulus ≤ input.left.val + input.right.val) :
    (eval spec input).val =
      input.left.val + input.right.val - spec.modulus := by
  have leftRange := input.left.isLt
  have rightRange := input.right.isLt
  have reducedRange :
      input.left.val + input.right.val - spec.modulus < spec.modulus := by
    omega
  rw [modularAdd_eval_val, Nat.mod_eq_sub_mod modulusLe,
    Nat.mod_eq_of_lt reducedRange]

@[simp] lemma modularAdd_eval_zero_left {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := Residue.zero spec, right := value } = value := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] lemma modularAdd_eval_zero_right {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := value, right := Residue.zero spec } = value := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt value.isLt]

end Add

namespace Sub

/-- Two canonical residues to subtract. -/
structure Input {width : Nat} (spec : ModulusSpec width) where
  /-- The minuend. -/
  left : Residue spec
  /-- The subtrahend. -/
  right : Residue spec
deriving DecidableEq

/-- Every pair of intrinsic residues is a valid modular-subtraction input. -/
@[nolint unusedArguments]
def valid {width : Nat} {spec : ModulusSpec width} (_input : Input spec) : Prop :=
  True

/-- A nonnegative representative whose reduction is `left - right` modulo `m`. -/
def difference {width : Nat} {spec : ModulusSpec width} (input : Input spec) : Nat :=
  input.left.val + spec.modulus - input.right.val

/-- Mathematical acceptance relation for modular subtraction. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Residue spec) : Prop :=
  output.val = difference input % spec.modulus

/-- The safe nonnegative difference representative fits in one additional bit. -/
lemma modularSub_difference_lt_extended {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    difference input < ClassicalAlgorithms.modulus (width + 1) := by
  have capacityPositive := ClassicalAlgorithms.fixedWidthModulus_pos width
  have modulusBound := spec.le_capacity
  have leftRange := input.left.isLt
  simp only [difference, ClassicalAlgorithms.modulus, pow_succ] at capacityPositive modulusBound ⊢
  omega

/-- The exact safe difference representative in one additional bit. -/
def differenceWord {width : Nat} {spec : ModulusSpec width} (input : Input spec) :
    Word (width + 1) :=
  ⟨difference input, modularSub_difference_lt_extended input⟩

@[simp] lemma modularSub_differenceWord_val {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    (differenceWord input).val = difference input :=
  rfl

/-- Canonical modular subtraction as reduction of a safe widened representative. -/
def eval {width : Nat} (spec : ModulusSpec width) (input : Input spec) :
    Residue spec :=
  Reduce.eval spec (differenceWord input)

@[simp] lemma modularSub_valid {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    valid input :=
  trivial

lemma modularSub_eval_eq_reduce {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = Reduce.eval spec (differenceWord input) :=
  rfl

@[simp] lemma modularSub_eval_val {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val = difference input % spec.modulus :=
  rfl

lemma modularSub_eval_range {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

lemma modularSub_eval_modEq {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val ≡ difference input [MOD spec.modulus] := by
  simpa only [modularSub_eval_eq_reduce, modularSub_differenceWord_val] using
    Reduce.modularReduce_eval_modEq spec (differenceWord input)

lemma modularSub_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    accepts input (eval spec input) :=
  rfl

/-- Borrowing subtraction wraps to `left + modulus - right`. -/
lemma modularSub_eval_val_of_lt {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) (borrow : input.left.val < input.right.val) :
    (eval spec input).val =
      input.left.val + spec.modulus - input.right.val := by
  have rightRange := input.right.isLt
  have wrappedRange :
      input.left.val + spec.modulus - input.right.val < spec.modulus := by
    omega
  rw [modularSub_eval_val]
  simp only [difference]
  rw [Nat.mod_eq_of_lt wrappedRange]

/-- Nonborrowing subtraction returns the ordinary natural difference. -/
lemma modularSub_eval_val_of_le {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) (rightLeLeft : input.right.val ≤ input.left.val) :
    (eval spec input).val = input.left.val - input.right.val := by
  have leftRange := input.left.isLt
  have differenceRange : input.left.val - input.right.val < spec.modulus := by
    omega
  have split : difference input =
      (input.left.val - input.right.val) + spec.modulus := by
    simp only [difference]
    omega
  rw [modularSub_eval_val, split]
  simp [Nat.mod_eq_of_lt differenceRange]

@[simp] lemma modularSub_eval_self {width : Nat} (spec : ModulusSpec width)
    (value : Residue spec) :
    eval spec { left := value, right := value } = Residue.zero spec := by
  apply Fin.ext
  simpa using modularSub_eval_val_of_le spec
    ({ left := value, right := value } : Input spec) le_rfl

@[simp] lemma modularSub_eval_zero_right {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := value, right := Residue.zero spec } = value := by
  apply Fin.ext
  simpa using modularSub_eval_val_of_le spec
    ({ left := value, right := Residue.zero spec } : Input spec) (Nat.zero_le _)

end Sub

namespace Neg

/-- One canonical residue to negate. -/
abbrev Input {width : Nat} (spec : ModulusSpec width) := Residue spec

/-- Every intrinsic residue is a valid modular-negation input. -/
@[nolint unusedArguments]
def valid {width : Nat} {spec : ModulusSpec width} (_input : Input spec) : Prop :=
  True

/-- A safe nonnegative representative of additive negation. -/
def negation {width : Nat} {spec : ModulusSpec width} (input : Input spec) : Nat :=
  spec.modulus - input.val

/-- Mathematical acceptance relation for modular negation. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Residue spec) : Prop :=
  output.val = negation input % spec.modulus

/-- The uniform negation representative fits in one additional bit. -/
lemma modularNeg_negation_lt_extended {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    negation input < ClassicalAlgorithms.modulus (width + 1) := by
  have capacityPositive := ClassicalAlgorithms.fixedWidthModulus_pos width
  have modulusBound := spec.le_capacity
  simp only [negation, ClassicalAlgorithms.modulus, pow_succ] at capacityPositive modulusBound ⊢
  omega

/-- The uniform negation representative in one additional bit. -/
def negationWord {width : Nat} {spec : ModulusSpec width} (input : Input spec) :
    Word (width + 1) :=
  ⟨negation input, modularNeg_negation_lt_extended input⟩

@[simp] lemma modularNeg_negationWord_val {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    (negationWord input).val = negation input :=
  rfl

/-- Canonical modular negation as reduction of a safe widened representative. -/
def eval {width : Nat} (spec : ModulusSpec width) (input : Input spec) :
    Residue spec :=
  Reduce.eval spec (negationWord input)

@[simp] lemma modularNeg_valid {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    valid input :=
  trivial

lemma modularNeg_eval_eq_reduce {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = Reduce.eval spec (negationWord input) :=
  rfl

@[simp] lemma modularNeg_eval_val {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val = negation input % spec.modulus :=
  rfl

lemma modularNeg_eval_range {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

lemma modularNeg_eval_modEq {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val ≡ negation input [MOD spec.modulus] := by
  simpa only [modularNeg_eval_eq_reduce, modularNeg_negationWord_val] using
    Reduce.modularReduce_eval_modEq spec (negationWord input)

lemma modularNeg_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    accepts input (eval spec input) :=
  rfl

@[simp] lemma modularNeg_eval_zero {width : Nat} (spec : ModulusSpec width) :
    eval spec (Residue.zero spec) = Residue.zero spec := by
  apply Fin.ext
  rw [modularNeg_eval_val]
  simp [negation]

lemma modularNeg_eval_val_of_pos {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) (inputPositive : 0 < input.val) :
    (eval spec input).val = spec.modulus - input.val := by
  have inputRange := input.isLt
  have negationRange : spec.modulus - input.val < spec.modulus := by
    omega
  rw [modularNeg_eval_val]
  simp only [negation]
  rw [Nat.mod_eq_of_lt negationRange]

lemma modularNeg_eval_val_of_ne_zero {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) (inputNonzero : input ≠ Residue.zero spec) :
    (eval spec input).val = spec.modulus - input.val := by
  apply modularNeg_eval_val_of_pos
  by_contra inputNotPositive
  have inputZero : input.val = 0 := Nat.eq_zero_of_not_pos inputNotPositive
  apply inputNonzero
  apply Fin.ext
  simp [inputZero]

lemma modularNeg_eval_eq_sub_zero {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input =
      Sub.eval spec { left := Residue.zero spec, right := input } := by
  apply Fin.ext
  simp [modularNeg_eval_val, Sub.modularSub_eval_val, negation, Sub.difference]

end Neg

namespace Double

/-- One canonical residue to double. -/
abbrev Input {width : Nat} (spec : ModulusSpec width) := Residue spec

/-- Every intrinsic residue is a valid modular-doubling input. -/
@[nolint unusedArguments]
def valid {width : Nat} {spec : ModulusSpec width} (_input : Input spec) : Prop :=
  True

/-- Mathematical acceptance relation for modular doubling. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Residue spec) : Prop :=
  output.val = (input.val + input.val) % spec.modulus

/-- Canonical doubling is addition with equal operands. -/
def eval {width : Nat} (spec : ModulusSpec width) (input : Input spec) :
    Residue spec :=
  Add.eval spec { left := input, right := input }

@[simp] lemma modularDouble_valid {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    valid input :=
  trivial

lemma modularDouble_eval_eq_add {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = Add.eval spec { left := input, right := input } :=
  rfl

@[simp] lemma modularDouble_eval_val {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val = (input.val + input.val) % spec.modulus :=
  Add.modularAdd_eval_val spec { left := input, right := input }

lemma modularDouble_eval_range {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

lemma modularDouble_eval_modEq {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val ≡ input.val + input.val [MOD spec.modulus] :=
  Add.modularAdd_eval_modEq spec { left := input, right := input }

lemma modularDouble_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    accepts input (eval spec input) :=
  modularDouble_eval_val spec input

@[simp] lemma modularDouble_eval_zero {width : Nat} (spec : ModulusSpec width) :
    eval spec (Residue.zero spec) = Residue.zero spec := by
  apply Fin.ext
  simp

end Double

end Modular

end ClassicalAlgorithms
end QuantumAlg

end
