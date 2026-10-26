/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Readout

/-! # All original metadata and the entire shared pool survive actual length alignment -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates

/-- Every original position after both complete work words is outside the executed target. -/
lemma gates_get_retained (width : Nat) (field : Field) (first : Bool)
    (observed : EncodedBit (encoding width)) (outside : 2 * (width + 3) ≤ observed.wire.val)
    (state : Data width) :
    observed.get (GateSpec.stepList (gates width field first) state) = observed.get state := by
  apply gates_get_outside
  intro index same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value] at values
  have within := index.isLt
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at values <;> omega

/-- Every bit of the unselected original work word remains present and unchanged. -/
lemma gates_other_word_get (width : Nat) (field : Field) (first : Bool)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width (!first) index).get
        (GateSpec.stepList (gates width field first) state) =
      (ArithmeticRotation.bit width (!first) index).get state := by
  apply gates_get_outside
  intro selected same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
  have left := selected.isLt
  have right := index.isLt
  cases first <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] at values
    <;> omega

/-- All actual address, prefix and conjunction systems retain their arbitrary original values. -/
lemma gates_pool (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    (GateSpec.stepList (gates width field first) state).2 = state.2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (addressBit width ⟨index, within⟩).wire.val := by
      rw [addressBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [addressBit_get] using
      gates_get_retained width field first (addressBit width ⟨index, within⟩) outside state
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (prefixBit width ⟨index, within⟩).wire.val := by
      rw [prefixBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [prefixBit_get] using
      gates_get_retained width field first (prefixBit width ⟨index, within⟩) outside state
  · have outside : 2 * (width + 3) ≤ (conjunctionBit width).wire.val := by
      rw [conjunctionBit_wire, SharedEEA.encoding_width]
      omega
    exact gates_get_retained width field first (conjunctionBit width) outside state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
