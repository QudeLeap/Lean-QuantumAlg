/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Bank
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.ManyDirty.Test
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Encoder

/-! # Actual first-one encoder using only the opposite existing arbitrary work word -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Native negative masks and borrowed-chain tests execute on the same existing full frame. -/
def program (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (bank width field first).policy.encoderProgram height capacity fits

/-- The actual faster native body has the exact original full first-one action on all inputs. -/
lemma program_realizes (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width field first height capacity fits)
      environment
      (GateSpec.stepList ((frame width field first).encoderGates height capacity fits)) :=
  (bank width field first).policy.policyEncoderProgram_realizes height capacity fits environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder
