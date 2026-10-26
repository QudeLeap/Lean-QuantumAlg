/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport

/-!
# Actual control transfers around full resident arithmetic

The body equation concerns the same physical resident program at its
actual cleared-pool input. Both paid enable directions and the complete
address suffix remain present. Arithmetic domain premises belong to the
body proof and must be discharged by the concrete state-chain consumer.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

/-- The two real temporary-control directions restore every original label. -/
lemma restore_prepare (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Control.restoreStep stream width bounded (Control.prepareStep stream width bounded state) =
      state := by
  unfold Control.restoreStep Control.prepareStep
  rw [Window.Enable.step_step]
  exact EncodedBit.cnotStep_cnotStep _ _ Control.flag_normal_ne state

lemma suffix_apply (body : Native.Circuit) (environment : OracleModel.empty.Interpretation)
    (initial final : Frame.Raw) (address : Window.Address)
    (actual : body.applyNormalized environment (Native.ket initial) = Native.ket final) :
    (Window.suffixProgram body).applyNormalized environment (Window.ket (initial, address)) =
      Window.ket (final, address) :=
  UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    Frame.encoding Window.addressEncoding body initial final address actual

/-- Genuine N is retained; the actual F toggle clears and then restores the enable. -/
lemma residentWithNormal_apply (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) (after : Frame.Raw)
    (actual : body.applyNormalized environment
      (Native.ket (Window.Enable.step stream width bounded state).1) = Native.ket after) :
    (residentWithNormal stream width bounded body).applyNormalized environment (Window.ket state) =
      Window.ket (Window.Enable.step stream width bounded
        (after, (Window.Enable.step stream width bounded state).2)) :=
  UnitaryCircuit.applyNormalized_seq_of_eq
    (Window.Enable.inverseProgram_ket stream width bounded environment state)
    (UnitaryCircuit.applyNormalized_seq_of_eq
      (suffix_apply body environment _ after _ actual)
      (Window.Enable.program_ket stream width bounded environment _))

/-- The actual temporary-N transfer is reversed after the same resident body. -/
lemma residentWithTemporary_apply (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) (after : Frame.Raw)
    (actual : body.applyNormalized environment
      (Native.ket (Control.prepareStep stream width bounded state).1) = Native.ket after) :
    (residentWithTemporary stream width bounded body).applyNormalized environment
        (Window.ket state) =
      Window.ket (Control.restoreStep stream width bounded
        (after, (Control.prepareStep stream width bounded state).2)) :=
  UnitaryCircuit.applyNormalized_seq_of_eq
    ((Control.prepare_realizes stream width bounded environment).apply_encoded_ket state)
    (UnitaryCircuit.applyNormalized_seq_of_eq
      (suffix_apply body environment _ after _ actual)
      ((Control.restore_realizes stream width bounded environment).apply_encoded_ket _))

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
