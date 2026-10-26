/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Rotation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Readout
import all QuantumAlg.Util.Nat.FixedWidth.Rotation

/-! # Original physical low-bit and unsigned readout of the native target rotation -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

/-- The physical rotation has the exact complete-width unsigned value used in modular doubling. -/
lemma rotation_target_value (state : Registers) :
    (stepList rotationGates state).1.2.val =
      Nat.FixedWidth.NearPower.rotatedWord capacity state.1.2.val := by
  rw [rotationGates_step]
  exact Nat.FixedWidth.Rotation.rotateLeft_one_toNat (by decide : 2 ≤ width)
    (BitVec.ofFin (w := width) state.1.2)

/-- The actual original low target wire now reads the overflow of the doubled original value. -/
lemma rotation_target_control (state : Registers) :
    targetLow.get (stepList rotationGates state) = decide (capacity ≤ 2 * state.1.2.val) := by
  rw [rotationGates_step]
  exact Nat.FixedWidth.Rotation.rotateLeft_one_low (by decide : 2 ≤ width)
    (BitVec.ofFin (w := width) state.1.2)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
