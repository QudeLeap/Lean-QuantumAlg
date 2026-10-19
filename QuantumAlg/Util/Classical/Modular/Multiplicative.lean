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

/-!
# Canonical multiplicative modular arithmetic

Multiplication and squaring first materialize the exact full-width mathematical
product and only then reduce it.  The public `fullProduct` witnesses rule out an
accidental low-word truncation before modular reduction.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace Modular

namespace Mul

/-- Two canonical residues to multiply. -/
structure Input {width : Nat} (spec : ModulusSpec width) where
  /-- The left factor. -/
  left : Residue spec
  /-- The right factor. -/
  right : Residue spec
deriving DecidableEq

/-- Every pair of intrinsic residues is a valid modular-multiplication input. -/
@[nolint unusedArguments]
def valid {width : Nat} {spec : ModulusSpec width} (_input : Input spec) : Prop :=
  True

/-- Mathematical acceptance relation for modular multiplication. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Residue spec) : Prop :=
  output.val = (input.left.val * input.right.val) % spec.modulus

/-- The exact, untruncated product in the combined operand width. -/
def fullProduct {width : Nat} {spec : ModulusSpec width} (input : Input spec) :
    Word (width + width) :=
  (ClassicalAlgorithms.MulFull.eval
    ({ left := input.left.toWord, right := input.right.toWord } :
      ClassicalAlgorithms.MulFull.Input width width)).value

@[simp] lemma modularMul_fullProduct_val {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    (fullProduct input).val = input.left.val * input.right.val := by
  change
    (ClassicalAlgorithms.MulFull.eval
      ({ left := input.left.toWord, right := input.right.toWord } :
        ClassicalAlgorithms.MulFull.Input width width)).value.val =
      input.left.val * input.right.val
  rw [ClassicalAlgorithms.MulFull.mulFull_eval_value]
  simp only [Residue.residueToWord_val]

lemma modularMul_fullProduct_range {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    (fullProduct input).val < ClassicalAlgorithms.modulus (width + width) :=
  ClassicalAlgorithms.fixedWidthWord_lt_modulus (fullProduct input)

/-- Canonical multiplication as reduction of the exact full-width product. -/
def eval {width : Nat} (spec : ModulusSpec width) (input : Input spec) :
    Residue spec :=
  Reduce.eval spec (fullProduct input)

@[simp] lemma modularMul_valid {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    valid input :=
  trivial

lemma modularMul_eval_eq_reduce {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = Reduce.eval spec (fullProduct input) :=
  rfl

@[simp] lemma modularMul_eval_val {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val =
      (input.left.val * input.right.val) % spec.modulus := by
  change (fullProduct input).val % spec.modulus = _
  rw [modularMul_fullProduct_val]

lemma modularMul_eval_range {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

lemma modularMul_eval_modEq {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val ≡
      input.left.val * input.right.val [MOD spec.modulus] := by
  rw [modularMul_eval_eq_reduce]
  simpa only [modularMul_fullProduct_val] using
    Reduce.modularReduce_eval_modEq spec (fullProduct input)

lemma modularMul_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    accepts input (eval spec input) :=
  modularMul_eval_val spec input

@[simp] lemma modularMul_eval_zero_left {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := Residue.zero spec, right := value } =
      Residue.zero spec := by
  apply Fin.ext
  simp

@[simp] lemma modularMul_eval_zero_right {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := value, right := Residue.zero spec } =
      Residue.zero spec := by
  apply Fin.ext
  simp

@[simp] lemma modularMul_eval_one_left {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := Residue.one spec, right := value } = value := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] lemma modularMul_eval_one_right {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    eval spec { left := value, right := Residue.one spec } = value := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt value.isLt]

end Mul

namespace Square

/-- One canonical residue to square. -/
abbrev Input {width : Nat} (spec : ModulusSpec width) := Residue spec

/-- Every intrinsic residue is a valid modular-squaring input. -/
@[nolint unusedArguments]
def valid {width : Nat} {spec : ModulusSpec width} (_input : Input spec) : Prop :=
  True

/-- Mathematical acceptance relation for modular squaring. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Residue spec) : Prop :=
  output.val = (input.val * input.val) % spec.modulus

/-- The exact, untruncated square in twice the operand width. -/
def fullProduct {width : Nat} {spec : ModulusSpec width} (input : Input spec) :
    Word (width + width) :=
  Mul.fullProduct { left := input, right := input }

@[simp] lemma modularSquare_fullProduct_val {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    (fullProduct input).val = input.val * input.val :=
  Mul.modularMul_fullProduct_val { left := input, right := input }

lemma modularSquare_fullProduct_range {width : Nat}
    {spec : ModulusSpec width} (input : Input spec) :
    (fullProduct input).val < ClassicalAlgorithms.modulus (width + width) :=
  ClassicalAlgorithms.fixedWidthWord_lt_modulus (fullProduct input)

/-- Canonical squaring is multiplication with equal operands. -/
def eval {width : Nat} (spec : ModulusSpec width) (input : Input spec) :
    Residue spec :=
  Mul.eval spec { left := input, right := input }

@[simp] lemma modularSquare_valid {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) :
    valid input :=
  trivial

lemma modularSquare_eval_eq_mul {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = Mul.eval spec { left := input, right := input } :=
  rfl

@[simp] lemma modularSquare_eval_val {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val = (input.val * input.val) % spec.modulus :=
  Mul.modularMul_eval_val spec { left := input, right := input }

lemma modularSquare_eval_range {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val < spec.modulus :=
  (eval spec input).isLt

lemma modularSquare_eval_modEq {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (eval spec input).val ≡ input.val * input.val [MOD spec.modulus] :=
  Mul.modularMul_eval_modEq spec { left := input, right := input }

lemma modularSquare_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    accepts input (eval spec input) :=
  modularSquare_eval_val spec input

@[simp] lemma modularSquare_eval_zero {width : Nat} (spec : ModulusSpec width) :
    eval spec (Residue.zero spec) = Residue.zero spec := by
  apply Fin.ext
  simp

@[simp] lemma modularSquare_eval_one {width : Nat} (spec : ModulusSpec width) :
    eval spec (Residue.one spec) = Residue.one spec := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt (modulusSpec_one_lt spec)]

end Square

end Modular

end ClassicalAlgorithms
end QuantumAlg

end
