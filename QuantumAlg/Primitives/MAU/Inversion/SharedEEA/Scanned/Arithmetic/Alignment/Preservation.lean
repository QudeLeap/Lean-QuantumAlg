/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Specification

/-! # Complete original metadata, flags and shared pool survive the actual two-word alignment -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Every original bit after the two full work words is outside each executed alignment stage. -/
lemma gates_get_retained (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (observed : EncodedBit (encoding width)) (outside : 2 * (width + 3) ≤ observed.wire.val)
    (state : Data width) :
    observed.get (GateSpec.stepList (gates width first field) state) = observed.get state := by
  apply gates_get_outside
  intro index same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value] at values
  have within := index.isLt
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at values <;> omega

/-- Both actual operand alignments retain every original outside quantum coordinate. -/
lemma pairGates_get_retained (width : Nat) (field : ArithmeticGeometry.Field)
    (observed : EncodedBit (encoding width)) (outside : 2 * (width + 3) ≤ observed.wire.val)
    (state : Data width) :
    observed.get (GateSpec.stepList (pairGates width field) state) = observed.get state := by
  rw [pairGates, GateSpec.stepList_append,
    gates_get_retained width false field observed outside,
    gates_get_retained width true field observed outside]

/-- The complete original address, every prefix and the separate conjunction remain unchanged. -/
lemma pairGates_pool (width : Nat) (field : ArithmeticGeometry.Field) (state : Data width) :
    (GateSpec.stepList (pairGates width field) state).2 = state.2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (addressBit width ⟨index, within⟩).wire.val := by
      rw [addressBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [addressBit_get] using
      pairGates_get_retained width field (addressBit width ⟨index, within⟩) outside state
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (prefixBit width ⟨index, within⟩).wire.val := by
      rw [prefixBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [prefixBit_get] using
      pairGates_get_retained width field (prefixBit width ⟨index, within⟩) outside state
  · have outside : 2 * (width + 3) ≤ (conjunctionBit width).wire.val := by
      rw [conjunctionBit_wire, SharedEEA.encoding_width]
      omega
    exact pairGates_get_retained width field (conjunctionBit width) outside state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
