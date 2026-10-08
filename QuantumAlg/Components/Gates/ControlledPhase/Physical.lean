/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.ControlledPhase.Semantics
import all QuantumAlg.Components.Gates.ControlledPhase.Semantics
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# The complete native controlled phase on selected ambient qubits

Control and target are distinct physical positions of dimension two. The
complete five-gate word is relocated there; every other ambient system keeps
its original dimension and state. No new controlled gate token is introduced.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

variable {count : Nat} (ambient : QuantumLayout count)
variable (control target : Fin count) (distinct : control ≠ target)
variable (controlQubit : (ambient.wire control).dimension = 2)
variable (targetQubit : (ambient.wire target).dimension = 2)

private def positions : Fin 2 ↪ Fin count where
  toFun := ![control, target]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

include controlQubit targetQubit in
private theorem dimensions (index : Fin 2) :
    (layout.wire index).dimension =
      (ambient.wire (positions control target distinct index)).dimension := by
  fin_cases index
  · exact controlQubit.symm
  · exact targetQubit.symm

/-- Place the independent exact controlled-phase target on the two requested physical wires. -/
public def placedOperator (angle : Real) : UnitaryOperator ambient.register :=
  UnitaryCircuit.operatorAt layout ambient (positions control target distinct)
    (dimensions ambient control target distinct controlQubit targetQubit) (operator angle)

/-- Run the entire native expansion at the requested control and target positions. -/
public def circuitAt (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles ambient :=
  UnitaryCircuit.placeAt layout ambient (positions control target distinct)
    (dimensions ambient control target distinct controlQubit targetQubit) (circuit oracles angle)

/-- The physically placed implementation retains the exact controlled phase on every input. -/
public theorem controlledPhase_circuitAt_matrix (oracles : OracleModel) (angle : Real) :
    (circuitAt ambient control target distinct controlQubit targetQubit oracles angle).matrix =
      placedOperator ambient control target distinct controlQubit targetQubit angle := by
  rw [circuitAt, UnitaryCircuit.placeAt_matrix, controlledPhase_circuit_matrix]
  rfl

/-- Placement retains all five actual native occurrences in their original order. -/
public theorem controlledPhase_circuitAt_events (oracles : OracleModel) (angle : Real) :
    (circuitAt ambient control target distinct controlQubit targetQubit oracles angle).eventTrace =
      [.gate .singleQubit, .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := by
  rw [circuitAt, UnitaryCircuit.placeAt_eventTrace, controlledPhase_circuit_events]

/-- The same serial implementation has depth five on every dimension-correct ambient layout. -/
public theorem controlledPhase_circuitAt_unit_depth (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
      (circuitAt ambient control target distinct controlQubit targetQubit oracles angle) = 5 := by
  change DepthExpr.depthEval (fun _ => 1)
    (circuitAt ambient control target distinct controlQubit targetQubit oracles angle).eventDepth =
      5
  rw [circuitAt, UnitaryCircuit.placeAt_eventDepth]
  exact controlledPhase_circuit_unit_depth oracles angle

end

end QuantumAlg.Gate.ControlledPhase
