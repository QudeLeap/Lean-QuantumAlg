/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Ext
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Remainder

/-!
# Original Ctrl remains independent of actual full-carry geometry preparation

The complete native geometry arithmetic neither reads nor changes
original Ctrl. Its all-label semantic commutation lets the actual
unitary adjoint restore the temporary target after the real predicate
has changed Ctrl, without erasing an address or high carry.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit

/-- Actual full-carry geometry commutes with the actual original Ctrl flip on every finite label. -/
lemma remainderStep_control_flip (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    remainderStep width positive ((sourceBit width (controlBit width)).flip state) =
      (sourceBit width (controlBit width)).flip (remainderStep width positive state) := by
  apply data_eq_of_source_prefix_target width
  · change (remainderStep width positive ((sourceBit width (controlBit width)).flip state)).1 =
      { (remainderStep width positive state).1 with
        control := !(remainderStep width positive state).1.control }
    rw [remainderStep_source, remainderStep_source]
    rfl
  · change (remainderStep width positive ((sourceBit width (controlBit width)).flip state)).2.2.1 =
      (remainderStep width positive state).2.2.1
    rw [remainderStep_prefix, remainderStep_prefix]
    rfl
  · change targetValue width
      (remainderStep width positive ((sourceBit width (controlBit width)).flip state)) =
        targetValue width (remainderStep width positive state)
    rw [remainderStep_targetValue, remainderStep_targetValue]
    rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
