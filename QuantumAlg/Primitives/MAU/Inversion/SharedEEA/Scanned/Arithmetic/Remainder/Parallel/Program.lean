/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Parallel.Pair
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Remainder
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Resources

/-! # Actual paired remainder preparation, arithmetic and its own adjoint -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel

noncomputable section

open EncodedBit

def prepareProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  (ArithmeticAddress.remainderProgram width positive).seq
    (ArithmeticAlignment.Parallel.pairProgram width .shift)

/-- The adjoint is of this same actual unitary preparation, with its real native layers. -/
def program (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  PredicateCompute.program (prepareProgram width positive) (RemainderWindow.program width signed)

def inverseProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  (program width positive signed).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- Signed subtraction and low addback retain the original source instruction selection. -/
def bodyProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  if signed then inverseProgram width positive true else program width positive false

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel
