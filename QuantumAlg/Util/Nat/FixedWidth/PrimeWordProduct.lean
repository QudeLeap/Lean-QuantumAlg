/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Permutation
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Nat.Prime.Basic

/-!
# Independent two-word prime-residue multiplication and division

The first word selects its mathematical residue unit on 0<X<p and the
identity unit elsewhere. The second word is multiplied by that unit (or
its inverse) when Y<p and remains fixed on the binary padding region.
The resulting two-word permutations are mutual inverses on all labels
and preserve X exactly [LYL+26, sec_point_add/sec_point_add.tex:24-36].

These total maps depend only on finite words and modular arithmetic.
They import no circuit, state, execution or native implementation. The
padding convention supplies a complete mathematical target and makes no
new implementation promise outside the original arithmetic input domain.
In particular canonical Y=0 is included in both in-place interfaces.
-/

namespace QuantumAlg.Nat.FixedWidth.PrimeWordProduct

noncomputable section

/-- Original nonzero canonical X determines its unit; all other first words select identity. -/
def factorUnit {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input : Fin (2 ^ width)) : (ZMod modulus.val)ˣ :=
  if valid : 0 < input.val ∧ input.val < modulus.val then
    ZMod.unitOfCoprime input.val
      ((Nat.coprime_of_lt_prime (Nat.ne_of_gt valid.1) valid.2 prime).symm)
  else 1

/-- On the original domain the selected mathematical unit is exactly X in the residue ring. -/
theorem factorUnit_coe {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input : Fin (2 ^ width))
    (positive : 0 < input.val) (bounded : input.val < modulus.val) :
    (factorUnit modulus prime input : ZMod modulus.val) = (input.val : ZMod modulus.val) := by
  unfold factorUnit
  split_ifs with valid
  · rfl
  · exact (valid ⟨positive, bounded⟩).elim

/-- The inverse unit is the ordinary modular inverse of the same original X. -/
theorem factorUnit_inv_coe {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input : Fin (2 ^ width))
    (positive : 0 < input.val) (bounded : input.val < modulus.val) :
    (((factorUnit modulus prime input)⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val) =
      (input.val : ZMod modulus.val)⁻¹ := by
  unfold factorUnit
  split_ifs with valid
  · rfl
  · exact (valid ⟨positive, bounded⟩).elim

/-- The non-domain first-word extension selects only the identity mathematical unit. -/
theorem factorUnit_other {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input : Fin (2 ^ width))
    (outside : ¬(0 < input.val ∧ input.val < modulus.val)) :
    factorUnit modulus prime input = 1 :=
  dif_neg outside

/-- Canonical modular inversion as an independent finite word, without any EEA implementation. -/
def inverseWord {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input : Fin (2 ^ width)) : Fin (2 ^ width) := by
  let : NeZero modulus.val := ⟨prime.ne_zero⟩
  exact ⟨((input.val : ZMod modulus.val)⁻¹).val,
    (ZMod.val_lt ((input.val : ZMod modulus.val)⁻¹)).trans_le
      (Nat.le_of_lt_succ modulus.isLt)⟩

/-- The inverse word stores exactly the canonical residue inverse. -/
theorem inverseWord_val {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input : Fin (2 ^ width)) :
    (inverseWord modulus prime input).val = ((input.val : ZMod modulus.val)⁻¹).val := rfl

/-- Independent two-word multiplication preserves X and permutes its complete Y word. -/
def multiplication {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) : Equiv.Perm (Fin (2 ^ width) × Fin (2 ^ width)) :=
  Equiv.prodCongrRight fun input =>
    unitProductWordPerm modulus prime.pos (factorUnit modulus prime input)

/-- Independent two-word division is the exact mathematical inverse of that multiplication. -/
def division {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) : Equiv.Perm (Fin (2 ^ width) × Fin (2 ^ width)) :=
  (multiplication modulus prime).symm

/-- The second word alone receives the selected unit product. -/
theorem multiplication_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width)) :
    multiplication modulus prime (input, numerator) =
      (input, unitProductWordPerm modulus prime.pos (factorUnit modulus prime input) numerator) :=
  rfl

/-- The inverse acts on the second word by the inverse of that same selected unit. -/
theorem division_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width)) :
    division modulus prime (input, numerator) =
      (input, unitProductWordPerm modulus prime.pos
        (factorUnit modulus prime input)⁻¹ numerator) := by
  change (input, (unitProductWordPerm modulus prime.pos
    (factorUnit modulus prime input)).symm numerator) = _
  rw [unitProductWordPerm_symm]

/-- Division restores every complete word pair after multiplication, including all padding. -/
theorem division_multiplication {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (state : Fin (2 ^ width) × Fin (2 ^ width)) :
    division modulus prime (multiplication modulus prime state) = state :=
  (multiplication modulus prime).symm_apply_apply state

/-- Multiplication likewise restores every complete pair after division. -/
theorem multiplication_division {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (state : Fin (2 ^ width) × Fin (2 ^ width)) :
    multiplication modulus prime (division modulus prime state) = state :=
  (multiplication modulus prime).apply_symm_apply state

/-- Original-domain multiplication has the canonical untruncated X*Y residue readout. -/
theorem multiplication_value {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width))
    (positive : 0 < input.val) (bounded : input.val < modulus.val)
    (numeratorBound : numerator.val < modulus.val) :
    (multiplication modulus prime (input, numerator)).2.val =
      (input.val * numerator.val) % modulus.val := by
  rw [multiplication_apply, unitProductWordPerm_valid modulus prime.pos _ numerator numeratorBound]
  change ((factorUnit modulus prime input : ZMod modulus.val).val * numerator.val) % modulus.val = _
  rw [factorUnit_coe modulus prime input positive bounded, ZMod.val_natCast_of_lt bounded]

/-- Original-domain division has the canonical inverse-X times Y residue readout. -/
theorem division_value {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width))
    (positive : 0 < input.val) (bounded : input.val < modulus.val)
    (numeratorBound : numerator.val < modulus.val) :
    (division modulus prime (input, numerator)).2.val =
      ((inverseWord modulus prime input).val * numerator.val) % modulus.val := by
  rw [division_apply, unitProductWordPerm_valid modulus prime.pos _ numerator numeratorBound]
  change ((((factorUnit modulus prime input)⁻¹ : (ZMod modulus.val)ˣ) :
    ZMod modulus.val).val * numerator.val) % modulus.val = _
  rw [factorUnit_inv_coe modulus prime input positive bounded, inverseWord_val]

/-- Y padding is fixed even when the first word is a valid nonzero residue. -/
theorem multiplication_padding {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width))
    (padding : ¬numerator.val < modulus.val) :
    multiplication modulus prime (input, numerator) = (input, numerator) := by
  rw [multiplication_apply, unitProductWordPerm_padding modulus prime.pos _ numerator padding]

/-- Division uses precisely the same identity convention on the Y padding region. -/
theorem division_padding {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width))
    (padding : ¬numerator.val < modulus.val) :
    division modulus prime (input, numerator) = (input, numerator) := by
  rw [division_apply, unitProductWordPerm_padding modulus prime.pos _ numerator padding]


/-- Multiplication preserves the entire first input word on all finite labels. -/
theorem multiplication_input {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (state : Fin (2 ^ width) × Fin (2 ^ width)) :
    (multiplication modulus prime state).1 = state.1 := rfl

/-- Division preserves the same entire first word, including its padding labels. -/
theorem division_input {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (state : Fin (2 ^ width) × Fin (2 ^ width)) :
    (division modulus prime state).1 = state.1 := rfl

/-- The complete mathematical extension is identity when original X is outside its domain. -/
theorem multiplication_other {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width))
    (outside : ¬(0 < input.val ∧ input.val < modulus.val)) :
    multiplication modulus prime (input, numerator) = (input, numerator) := by
  rw [multiplication_apply, factorUnit_other modulus prime input outside,
    unitProductWordPerm_one, Equiv.refl_apply]

/-- The inverse uses exactly the same identity extension for non-domain X. -/
theorem division_other {width : Nat} (modulus : Fin (2 ^ width + 1))
    (prime : Nat.Prime modulus.val) (input numerator : Fin (2 ^ width))
    (outside : ¬(0 < input.val ∧ input.val < modulus.val)) :
    division modulus prime (input, numerator) = (input, numerator) := by
  rw [division_apply, factorUnit_other modulus prime input outside, inv_one,
    unitProductWordPerm_one, Equiv.refl_apply]

end

end QuantumAlg.Nat.FixedWidth.PrimeWordProduct
