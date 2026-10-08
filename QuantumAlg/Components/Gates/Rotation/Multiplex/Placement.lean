/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex.Semantics
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Diagonal

/-!
# Native rotation selection on original ambient qubits

The selector and target remain their specified ambient wires. All other
qubits, including entangled work and source registers, retain their state.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex
noncomputable section

variable {width : Nat} (selector target : Fin width) (distinct : selector ≠ target)

private def positions : Fin 2 ↪ Fin width where
  toFun := ![selector, target]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

/-- Relocate the complete four-gate word to the requested original selector and target. -/
def circuitAt (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout :=
  UnitaryCircuit.placeAt layout (QuantumSignature.qubits width).canonicalPlacement.layout
    (positions selector target distinct) (fun _ => rfl) (circuit oracles zeroAngle oneAngle)

/-- Full ambient matrix of coherent phase selection, with every spectator unchanged. -/
theorem circuitAt_matrix (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    ((circuitAt selector target distinct oracles zeroAngle oneAngle).matrix :
      HilbertOperator (QuantumSignature.qubits width).canonicalPlacement.layout.register) =
        Matrix.diagonal (fun basis =>
          weight (if basis selector = 0 then zeroAngle else oneAngle) (basis target)) := by
  rw [circuitAt, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_diagonal layout
    (QuantumSignature.qubits width).canonicalPlacement.layout
    (positions selector target distinct) (fun _ => rfl)
    (circuit oracles zeroAngle oneAngle).matrix _ (circuit_matrix oracles zeroAngle oneAngle)

/-- Ambient placement retains every original native event. -/
theorem circuitAt_eventTrace (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    (circuitAt selector target distinct oracles zeroAngle oneAngle).eventTrace =
      [.gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := by
  rw [circuitAt, UnitaryCircuit.placeAt_eventTrace, circuit_eventTrace]

/-- Placement preserves all four native dependencies within the surrounding execution. -/
theorem circuitAt_depth (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    (circuitAt selector target distinct oracles zeroAngle oneAngle).evaluatedEventDepth
      (fun _ => 1) = 4 := by
  change DepthExpr.depthEval (fun _ => 1)
    (circuitAt selector target distinct oracles zeroAngle oneAngle).eventDepth = 4
  rw [circuitAt, UnitaryCircuit.placeAt_eventDepth]
  exact circuit_depth oracles zeroAngle oneAngle

end
end QuantumAlg.Gate.Rotation.Multiplex
