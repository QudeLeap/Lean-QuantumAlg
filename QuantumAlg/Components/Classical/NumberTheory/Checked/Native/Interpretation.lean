/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Raw
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Engine.Model

/-!
# Actual widened words and the original checked-inverse input

The real modulus word has the extra bit required for a capacity modulus.
The original denominator is widened by the actual resize instruction. Their
exact natural values identify the original mathematical XGCD input without
adding a primality, nonzero-denominator or inverse-correctness premise.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open ClassicalAlgorithms.Modular

private lemma checkedInput_word_eq {width : Nat} (left right : CShape.Word width)
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right =>
          exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- The actual two operand words are exactly the original modulus-left XGCD input. -/
lemma widenedXgcdInput_eq_xgcdInput {width : Nat} (spec : ModulusSpec width)
    (modulus : CShape.Word (width + 1)) (raw : CShape.Word width)
    (denominator : Residue spec) (modulusValue : modulus.toNat = spec.modulus)
    (represented : raw.toNat = denominator.val) :
    widenedXgcdInput modulus raw = Engine.xgcdInput spec denominator := by
  have leftWord : modulus = CShape.wordOfNat (width + 1) spec.modulus := by
    apply checkedInput_word_eq
    exact modulusValue.trans (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec)).symm
  have rightWord : CShape.wordResize (width + 1) raw =
      CShape.wordOfNat (width + 1) denominator.val := by
    apply checkedInput_word_eq
    change raw.toNat % 2 ^ (width + 1) = denominator.val % 2 ^ (width + 1)
    rw [represented]
  unfold widenedXgcdInput
  rw [leftWord, rightWord]
  rfl

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
