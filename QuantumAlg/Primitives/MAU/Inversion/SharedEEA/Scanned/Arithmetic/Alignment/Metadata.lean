/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Preservation

/-! # Actual two-word alignment retains complete original metadata and source control -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit

/-- Every complete original finite metadata operand survives both actual native barrels. -/
lemma pairGates_fieldValue (width : Nat) (field observed : ArithmeticGeometry.Field)
    (state : Data width) :
    ArithmeticGeometry.fieldValue observed (GateSpec.stepList (pairGates width field) state) =
      ArithmeticGeometry.fieldValue observed state := by
  rw [pairGates, GateSpec.stepList_append, gates_fieldValue, gates_fieldValue]

/-- The original arbitrary source control remains outside both actual aligned work words. -/
lemma pairGates_control (width : Nat) (field : ArithmeticGeometry.Field) (state : Data width) :
    (GateSpec.stepList (pairGates width field) state).1.control = state.1.control := by
  apply pairGates_get_retained width field (sourceBit width (SharedEEA.controlBit width))
  rw [sourceBit_wire, SharedEEA.controlBit_wire]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
