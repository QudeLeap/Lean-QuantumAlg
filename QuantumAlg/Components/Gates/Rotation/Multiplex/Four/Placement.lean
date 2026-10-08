/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex.Four.Semantics
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Diagonal

/-!
# Four selected rotations ahead of an untouched source suffix

The original three prefix wires remain two selectors and one phase target.
Placement preserves the native word and every arbitrary source correlation.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex.Four
noncomputable section

private def prefixPositions (width : Nat) : Fin 3 ↪ Fin (1 + (1 + (1 + width))) where
  toFun index := ⟨index.val, by have bound := index.isLt; omega⟩
  inj' := by
    intro left right same
    apply Fin.ext
    exact congrArg (fun index : Fin (1 + (1 + (1 + width))) => index.val) same

/-- Place the actual ten-gate selector word before the unchanged source suffix. -/
def onPrefix (oracles : OracleModel) (width : Nat) (a00 a01 a10 a11 : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + (1 + (1 + width)))).canonicalPlacement.layout :=
  UnitaryCircuit.placeAt layout
    (QuantumSignature.qubits (1 + (1 + (1 + width)))).canonicalPlacement.layout
    (prefixPositions width) (fun _ => rfl) (circuit oracles a00 a01 a10 a11)

/-- The entire physical matrix is diagonal with the supplied coherent angle choice. -/
theorem fourRotation_prefix_matrix (oracles : OracleModel) (width : Nat)
    (a00 a01 a10 a11 : ℝ) :
    ((onPrefix oracles width a00 a01 a10 a11).matrix :
      HilbertOperator
        (QuantumSignature.qubits (1 + (1 + (1 + width)))).canonicalPlacement.layout.register) =
      Matrix.diagonal (fun basis => weight
        (if basis (prefixPositions width 0) = 0 then
          (if basis (prefixPositions width 1) = 0 then a00 else a01)
        else (if basis (prefixPositions width 1) = 0 then a10 else a11))
        (basis (prefixPositions width 2))) := by
  rw [onPrefix, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_diagonal layout _ (prefixPositions width) (fun _ => rfl)
    (circuit oracles a00 a01 a10 a11).matrix _ (fourRotation_matrix oracles a00 a01 a10 a11)

/-- Placement preserves all four rotations and six CNOTs without source queries. -/
theorem fourRotation_prefix_eventTrace (oracles : OracleModel) (width : Nat)
    (a00 a01 a10 a11 : ℝ) :
    (onPrefix oracles width a00 a01 a10 a11).eventTrace =
      [.gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot,
        .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot] := by
  rw [onPrefix, UnitaryCircuit.placeAt_eventTrace, fourRotation_eventTrace]

/-- The unchanged source suffix adds no operation to the ten-step native word. -/
theorem fourRotation_prefix_depth (oracles : OracleModel) (width : Nat)
    (a00 a01 a10 a11 : ℝ) :
    (onPrefix oracles width a00 a01 a10 a11).evaluatedEventDepth (fun _ => 1) = 10 := by
  change DepthExpr.depthEval (fun _ => 1) (onPrefix oracles width a00 a01 a10 a11).eventDepth = 10
  rw [onPrefix, UnitaryCircuit.placeAt_eventDepth]
  exact fourRotation_depth oracles a00 a01 a10 a11

end
end QuantumAlg.Gate.Rotation.Multiplex.Four
