/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ControlledZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.FinPow

/-!
# Elementary controlled source reflection with an existing phase wire as work

The program uses two distinct original phase positions as control and work.
Its complete phase/source basis action is exactly controlled positive zero
reflection; every original phase value, including the arbitrary work value,
is restored. No new qubit or product-state input promise is introduced.
-/

namespace QuantumAlg.ZeroReflection.PhaseWorkspace

noncomputable section

/-- Execute the actual controlled elementary construction on the existing complete register. -/
def program (oracles : OracleModel) (phases controls : Nat)
    (physical : QubitLayout (phases + (controls + 1))) (control work : Fin phases)
    (different : control ≠ work) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (layout phases controls work).controlledZeroReflectionProgram physical oracles
    (phaseBit phases controls control)
    (control_source_ne phases controls control work)
    (control_output_ne phases controls control work)
    (control_work_ne phases controls control work different)

/-- Exact full-register action preserves every phase value on both control branches. -/
theorem program_applyVec_pair (oracles : OracleModel) (phases controls : Nat)
    (physical : QubitLayout (phases + (controls + 1))) (control work : Fin phases)
    (different : control ≠ work) (phase : Fin (2 ^ phases))
    (source : Fin (2 ^ (controls + 1))) :
    (program oracles phases controls physical control work different).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (prodEquiv (phase, source)))).vec =
      if (BinaryLabelEncoding.finIdentityBit phases control).get phase then
        if source = 0 then
          (NormalizedVector.ket (R := physical.toQuantum.register)
            (physical.basisEquiv.symm (prodEquiv (phase, source)))).vec
        else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (prodEquiv (phase, source)))).vec
      else (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (prodEquiv (phase, source)))).vec := by
  have encoded : (encoding phases controls).encode (phase, source) =
      prodEquiv (phase, source) := rfl
  have actual := (layout phases controls work).controlledZeroReflectionProgram_applyVec_encoded_ket
      physical oracles
    (phaseBit phases controls control)
    (control_source_ne phases controls control work)
    (control_output_ne phases controls control work)
    (control_work_ne phases controls control work different) (phase, source)
  change (program oracles phases controls physical control work different).applyVec
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm ((encoding phases controls).encode (phase, source)))).vec =
    (if (phaseBit phases controls control).get (phase, source) then
      if (layout phases controls work).reflectedZero (phase, source) then
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm ((encoding phases controls).encode (phase, source)))).vec
      else -(NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm ((encoding phases controls).encode (phase, source)))).vec
    else (NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm ((encoding phases controls).encode (phase, source)))).vec) at actual
  simpa only [reflectedZero_iff, phaseBit_get, encoded] using actual

/-- The actual elementary event trace has a linear source-width bound with no extra wire. -/
theorem program_eventTrace_length_le (oracles : OracleModel) (phases controls : Nat)
    (physical : QubitLayout (phases + (controls + 1))) (control work : Fin phases)
    (different : control ≠ work) :
    (program oracles phases controls physical control work different).eventTrace.length ≤
      10 * (controls + 1) + 4 :=
  (layout phases controls work).controlledZeroReflectionProgram_eventTrace_length_le
      physical oracles
    (phaseBit phases controls control)
    (control_source_ne phases controls control work)
    (control_output_ne phases controls control work)
    (control_work_ne phases controls control work different)

end

end QuantumAlg.ZeroReflection.PhaseWorkspace
