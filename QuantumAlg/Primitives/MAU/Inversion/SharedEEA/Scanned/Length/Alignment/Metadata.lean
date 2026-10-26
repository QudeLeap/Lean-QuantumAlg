/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment.Preservation

/-! # Complete retained control and boundary-key values of the actual length alignment -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The actual complete other length remains the original boundary, on every finite label. -/
lemma gates_boundary (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    boundaryValue field (GateSpec.stepList (gates width field first) state).1 =
      boundaryValue field state.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have retained := gates_get_retained width field first
    (sourceBit width (boundaryBit width field ⟨index, within⟩))
    (by rw [sourceBit_wire, boundaryBit_wire]; omega) state
  simpa only [sourceBit_get, boundaryBit_get] using retained

/-- The retained original Ctrl does not change when either work word is aligned. -/
lemma gates_control (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    (GateSpec.stepList (gates width field first) state).1.control = state.1.control :=
  gates_get_retained width field first (sourceBit width (SharedEEA.controlBit width))
    (by rw [sourceBit_wire, SharedEEA.controlBit_wire]; omega) state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
