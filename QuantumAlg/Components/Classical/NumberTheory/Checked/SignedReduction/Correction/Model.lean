/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Model

/-!
# Original pure signed-correction arithmetic

The original widened subtraction and zero-remainder normalization proofs
are independent of machine execution. Their original names and bodies are
preserved, including the full-capacity modulus boundary.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction

open ClassicalAlgorithms ClassicalAlgorithms.NumberTheory ClassicalAlgorithms.Modular

/-- Wrapping subtraction agrees with ordinary subtraction when the right
operand is no larger than the left operand. -/
lemma widenedWordSub_exact_of_le {width : Nat}
    (left right : CShape.Word (xgcdWidth width))
    (rightLe : right.toNat ≤ left.toNat) :
    (CShape.wordSub (xgcdWidth width) left right).toNat =
      left.toNat - right.toNat := by
  have leftRange :
      left.toNat < CShape.wordModulus (xgcdWidth width) :=
    left.toNat_lt
  have differenceRange :
      left.toNat - right.toNat < CShape.wordModulus (xgcdWidth width) :=
    (Nat.sub_le _ _).trans_lt leftRange
  have wrappedSplit :
      left.toNat + CShape.wordModulus (xgcdWidth width) - right.toNat =
        (left.toNat - right.toNat) +
          CShape.wordModulus (xgcdWidth width) := by
    omega
  rw [CShape.wordSub, CShape.wordOfNat_val, wrappedSplit]
  simp [Nat.mod_eq_of_lt differenceRange]

/-- Reducing `modulus - remainder` performs the required zero normalization.
The statement does not assume that the modulus is strictly below capacity, so
it also covers the `modulus = 2 ^ width` boundary. -/
lemma correctionRemainder_eq_normalized {width : Nat}
    (spec : ModulusSpec width) (remainder : Nat)
    (remainderRange : remainder < spec.modulus) :
    (spec.modulus - remainder) % spec.modulus =
      if remainder = 0 then 0 else spec.modulus - remainder := by
  by_cases remainderZero : remainder = 0
  · simp [remainderZero]
  · have correctedRange :
        spec.modulus - remainder < spec.modulus := by
      omega
    simp [remainderZero, Nat.mod_eq_of_lt correctedRange]

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction
