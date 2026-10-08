/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Two selected Z rotations from an actual native word

One selector chooses between two supplied angles coherently. The expansion
uses two one-qubit rotations and two CNOTs. It introduces no controlled-unitary
oracle access and retains the full phase of both branches.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex
noncomputable section

/-- Original selector and target, in that physical order. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- Actual average/difference rotations with their two native CNOT occurrences. -/
def circuit (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let average := singleQubitAt layout oracles (rotZStdOp ((zeroAngle + oneAngle) / 2)) 1 rfl
  let difference := singleQubitAt layout oracles (rotZStdOp ((zeroAngle - oneAngle) / 2)) 1 rfl
  let cnot : UnitaryCircuit AlgorithmGate.model oracles layout :=
    .native (GateModel.Application.canonical AlgorithmGate.model .cnot)
  ((average.seq cnot).seq difference).seq cnot

/-- Coherent selection retains all four actual native events. -/
theorem circuit_eventTrace (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    (circuit oracles zeroAngle oneAngle).eventTrace =
      [.gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := rfl

/-- Both native rotations and both CNOTs contribute to the same dependency chain. -/
theorem circuit_depth (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    (circuit oracles zeroAngle oneAngle).evaluatedEventDepth (fun _ => 1) = 4 := rfl

end
end QuantumAlg.Gate.Rotation.Multiplex
