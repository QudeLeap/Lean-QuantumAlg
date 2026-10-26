/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Projection
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Constant
import Mathlib.Algebra.BigOperators.Fin

/-!
# Common physical H amplitude and its retained measured character

The coefficient of the actual parallel H bank is its positive common
amplitude times the product of its original bit characters. The same
character is the parity of a named original mask and table word; this is
an algebraic identity, not a grant of a free feedback computation.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

open NormalizedVector
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma hadamard_entry_character (row column : Fin 2) :
    Gate.HOp row column = invSqrt2 *
      (if row.val = 1 ∧ column.val = 1 then (-1 : ℂ) else 1) := by
  fin_cases row <;> fin_cases column <;>
    simp [Gate.HOp, UnitaryOperator.ofMatrix, smul_eq_mul]

/-- Exact product of the retained original physical measurement characters. -/
def wordHadamardCharacter (physical : QubitLayout encoding.width) (target : Word encoding width)
    (row column : physical.toQuantum.Basis) : ℂ :=
  ∏ index : Fin width,
    if (row (target.bit index).wire).val = 1 ∧ (column (target.bit index).wire).val = 1
      then -1 else 1

/-- Every actual H column has the same positive amplitude and its exact original bit character. -/
lemma wordHadamardAmplitude_character (physical : QubitLayout encoding.width)
    (target : Word encoding width) (row column : physical.toQuantum.Basis) :
    wordHadamardAmplitude physical target row column =
      invSqrt2 ^ width * wordHadamardCharacter physical target row column := by
  unfold wordHadamardAmplitude wordHadamardCharacter
  simp_rw [hadamard_entry_character]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- Each original retained bit character is a real sign and squares to one. -/
lemma wordHadamardCharacter_sq (physical : QubitLayout encoding.width)
    (target : Word encoding width) (row column : physical.toQuantum.Basis) :
    wordHadamardCharacter physical target row column *
        wordHadamardCharacter physical target row column = 1 := by
  unfold wordHadamardCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro index _
  split_ifs <;> norm_num

private lemma sign_xor (first second : Bool) :
    (if first ^^ second then (-1 : ℂ) else 1) =
      (if first then (-1 : ℂ) else 1) * (if second then (-1 : ℂ) else 1) := by
  cases first <;> cases second <;> norm_num

private lemma sign_foldr {Index : Type} (indices : List Index) (bits : Index → Bool) :
    (if indices.foldr (fun index tail => bits index ^^ tail) false then (-1 : ℂ) else 1) =
      (indices.map fun index => if bits index then (-1 : ℂ) else 1).prod := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons, ← ih, sign_xor]

private lemma product_filter {Index : Type} (indices : List Index)
    (predicate : Index → Bool) (value : Index → ℂ) :
    ((indices.filter predicate).map value).prod =
      (indices.map fun index => if predicate index then value index else 1).prod := by
  induction indices with
  | nil => rfl
  | cons first rest ih => cases chosen : predicate first <;> simp [chosen, ih]

/-- The paid row parity character is exactly the full product over original mask and table bits. -/
lemma maskCharacter_eq_prod (mask : CShape.Value (.bits width)) (constant : Fin (2 ^ width)) :
    (if MaskParity.maskValue mask constant then (-1 : ℂ) else 1) =
      ∏ index : Fin width, if constant.val.testBit index.val then
        (if (mask.bitGet index).toBool then (-1 : ℂ) else 1) else 1 := by
  rw [MaskParity.maskValue, sign_foldr, Word.constantOneIndices, product_filter,
    List.map_ofFn, List.prod_ofFn]
  rfl

/-- The actual original physical character agrees with its actual measured mask and table word. -/
lemma wordHadamardCharacter_mask (physical : QubitLayout encoding.width)
    (target : Word encoding width) (row column : physical.toQuantum.Basis)
    (mask : CShape.Value (.bits width)) (constant : Fin (2 ^ width))
    (rowBits : ∀ index, (mask.bitGet index).toBool =
      decide ((row (target.bit index).wire).val = 1))
    (columnBits : ∀ index, constant.val.testBit index.val =
      decide ((column (target.bit index).wire).val = 1)) :
    wordHadamardCharacter physical target row column =
      if MaskParity.maskValue mask constant then (-1 : ℂ) else 1 := by
  rw [maskCharacter_eq_prod]
  unfold wordHadamardCharacter
  apply Finset.prod_congr rfl
  intro index _
  rw [rowBits, columnBits]
  by_cases rowOne : (row (target.bit index).wire).val = 1 <;>
    by_cases columnOne : (column (target.bit index).wire).val = 1 <;> simp [rowOne, columnOne]

end

end QuantumAlg.EncodedBit.WindowLookup
