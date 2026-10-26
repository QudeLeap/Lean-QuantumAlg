/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Parallel.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Toggle
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Body
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Sandwich
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement

/-! # Actual selected paired arithmetic in original source order -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

open EncodedBit

def arithmeticBody (width : Nat) (positive : 1 ≤ width) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  if coefficient then CoefficientGuard.bodyProgram width positive signed
  else RemainderAddress.Parallel.bodyProgram width positive signed

/-- Both paid fused guards surround the same original source body on its actual physical prefix. -/
def instructionProgram (width : Nat) (positive : 1 ≤ width) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  SelectedSandwich.program (Scanned.encoding width)
    (arithmeticBody width positive signed coefficient)
    (ControlledArithmeticToggle.program width positive signed coefficient)

/-- Both actual source instructions and their complete original Sign update remain chronological. -/
def arithmeticProgram (width : Nat) (positive : 1 ≤ width) (coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (instructionProgram width positive (!coefficient) coefficient).seq
    ((ControlledSourceWord.program width
      (ControlledArithmeticBlocks.signGates width coefficient)).seq
        (instructionProgram width positive coefficient coefficient))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
