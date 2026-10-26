/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Specification

/-! # Independent serial two-word alignment on the original full carrier -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit

/-- The literal joint alignment has complete coherent native semantics on the same carrier. -/
def pairProgram (width : Nat) (field : ArithmeticGeometry.Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (pairGates width field)

/-- Every original system and arbitrary reference amplitude follows the full emitted gate word. -/
lemma pairProgram_realizes (width : Nat) (field : ArithmeticGeometry.Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (pairProgram width field) environment
      (GateSpec.stepList (pairGates width field)) :=
  GateSpec.realizesList (QubitLayout.canonical _) .empty _ environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
