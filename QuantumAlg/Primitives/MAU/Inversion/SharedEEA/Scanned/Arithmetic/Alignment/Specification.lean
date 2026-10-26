/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Window

/-! # Complete two-word alignment permutation and retention laws -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit

/-- All positions in the other complete original word retain their arbitrary original values. -/
lemma gates_other_word_get (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width (!first) index).get
        (GateSpec.stepList (gates width first field) state) =
      (ArithmeticRotation.bit width (!first) index).get state := by
  apply gates_get_outside
  intro wordIndex same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
  have left := wordIndex.isLt
  have right := index.isLt
  cases first <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] at values
    <;> omega

/-- The complete alignment executes actual Fredkin stages on both existing physical words. -/
def pairGates (width : Nat) (field : ArithmeticGeometry.Field) :
    List (GateSpec (encoding width)) :=
  gates width true field ++ gates width false field

/-- Both full operands have the exact original complete-metadata displacement. -/
lemma pairGates_bit_get (width : Nat) (field : ArithmeticGeometry.Field) (first : Bool)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width first index).get
        (GateSpec.stepList (pairGates width field) state) =
      (ArithmeticRotation.bit width first
        ((permutation width ^ (ArithmeticGeometry.fieldValue field state).toNat) index)).get
        state := by
  rw [pairGates, GateSpec.stepList_append]
  cases first with
  | false =>
      rw [gates_bit_get, gates_fieldValue]
      exact gates_other_word_get width true field _ state
  | true =>
      exact (gates_other_word_get width false field index _).trans
        (gates_bit_get width true field index state)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
