/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Registers
import all QuantumAlg.Util.Permutation.Rotation

/-!
# Actual barrel readouts are exactly the original remainder window positions

The original physical prefix, arithmetic window and suffix partition
the complete unchanged work word. Negative readout displacement by the
original shift moves the selected slice to the template's low bits.
Every selected bit is proved nonwrapping; no bits are dropped or reset.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit

private def lowIndex {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (index : Fin window.length) : Fin (width + 3) :=
  ⟨width + 3 - 1 - index.val, by
    have complete := window.complete
    have within := index.isLt
    omega⟩

/-- Every actual template bit receives exactly the corresponding original arithmetic slice bit. -/
lemma gates_window_bit_get (width : Nat) (first : Bool)
    (window : ArithmeticWindowRegisters.Window width) (index : Fin window.length)
    (state : Data width) (shift : state.1.shift.toNat = window.below) :
    (ArithmeticRotation.bit width first (lowIndex window index)).get
        (GateSpec.stepList (gates width first .shift) state) =
      (ArithmeticRotation.bit width first (ArithmeticWindowRegisters.windowIndex window index)).get
        state := by
  have : NeZero (width + 3) := ⟨by omega⟩
  have fits : state.1.shift.toNat ≤ (lowIndex window index).val := by
    rw [shift]
    change window.below ≤ width + 3 - 1 - index.val
    have complete := window.complete
    have within := index.isLt
    omega
  have moved := Permutation.inverseRotation_pow_apply_of_le state.1.shift.toNat
    (lowIndex window index) fits
  have position : ((permutation width ^ state.1.shift.toNat) (lowIndex window index)) =
      ArithmeticWindowRegisters.windowIndex window index := by
    apply Fin.ext
    change (((finRotate (width + 3))⁻¹ ^ state.1.shift.toNat)
      (lowIndex window index)).val = window.above + (window.length - 1 - index.val)
    rw [moved, shift]
    change width + 3 - 1 - index.val - window.below =
      window.above + (window.length - 1 - index.val)
    have complete := window.complete
    have within := index.isLt
    omega
  have actual := gates_bit_get width first .shift (lowIndex window index) state
  simpa only [ArithmeticGeometry.fieldValue, position] using actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
