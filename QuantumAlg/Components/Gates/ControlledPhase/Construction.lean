/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.ControlledPhase.Operator
import all QuantumAlg.Components.Gates.ControlledPhase.Operator
public import QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Native phase and CNOT word for controlled phase

The implementation contains three actual one-qubit phase gates and two actual
CNOTs, with both physical qubits present throughout. The original addressed
controlled-phase operator is an independent target. The macro retains the
entire native word, including every sequential event and dependency.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The two ordered physical qubits of the local expansion. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- The unchanged addressed controlled-phase target in the physical-layout basis. -/
public def operator (angle : Real) : UnitaryOperator layout.register :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm
    (qftControlledPhaseOperator (n := 2) 0 1 angle)

/-- Execute all three phase gates and both CNOTs without a new controlled-gate token. -/
public def circuit (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let first := singleQubitAt layout oracles (phaseGateOp (angle / 2)) 0 rfl
  let second := singleQubitAt layout oracles (phaseGateOp (angle / 2)) 1 rfl
  let middle := singleQubitAt layout oracles (phaseGateOp (-(angle / 2))) 1 rfl
  let controlled : UnitaryCircuit AlgorithmGate.model oracles layout :=
    .native (GateModel.Application.canonical AlgorithmGate.model .cnot)
  .macroCall "controlled-phase" ((((first.seq second).seq controlled).seq middle).seq controlled)

/-- The macro records the five actual native occurrences in their execution order. -/
public theorem controlledPhase_circuit_events (oracles : OracleModel) (angle : Real) :
    (circuit oracles angle).eventTrace =
      [.gate .singleQubit, .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := by
  rfl

/-- The chosen serial word has all five native dependencies in the same circuit period. -/
public theorem controlledPhase_circuit_unit_depth (oracles : OracleModel) (angle : Real) :
    (circuit oracles angle).evaluatedEventDepth (fun _ => 1) = 5 := by
  rfl

/-- One descriptive annotation accompanies the complete retained native expansion. -/
public theorem controlledPhase_circuit_macro_count (oracles : OracleModel) (angle : Real) :
    (circuit oracles angle).macroCount "controlled-phase" = 1 := by
  rfl

end

end QuantumAlg.Gate.ControlledPhase
