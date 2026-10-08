/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Components.Gates.Swap.Controlled
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Actual controlled exchange on three selected ambient qubits

The original control and both targets must be distinct dimension-two systems.
The complete CNOT/Toffoli/CNOT implementation preserves every other physical
system without imposing a dimension or initialization premise on spectators.
-/

namespace QuantumAlg.Gate.ControlledSwap

noncomputable section

variable {count : Nat} (ambient : QuantumLayout count)
variable (control left right : Fin count)
variable (controlLeft : control ≠ left) (controlRight : control ≠ right) (leftRight : left ≠ right)
variable (controlQubit : (ambient.wire control).dimension = 2)
variable (leftQubit : (ambient.wire left).dimension = 2)
variable (rightQubit : (ambient.wire right).dimension = 2)

private def positions : Fin 3 ↪ Fin count where
  toFun := ![control, left, right]
  inj' := by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all

include controlQubit leftQubit rightQubit in
private theorem dimensions (index : Fin 3) :
    (layout.wire index).dimension =
      (ambient.wire
        (positions control left right controlLeft controlRight leftRight index)).dimension := by
  fin_cases index
  · exact controlQubit.symm
  · exact leftQubit.symm
  · exact rightQubit.symm

/-- The independent exact controlled exchange on the three selected physical positions. -/
public def placedOperator : UnitaryOperator ambient.register :=
  UnitaryCircuit.operatorAt layout ambient
    (positions control left right controlLeft controlRight leftRight)
    (dimensions ambient control left right controlLeft controlRight leftRight
      controlQubit leftQubit rightQubit) operator

/-- Relocate the complete native implementation without adding a gate or workspace. -/
public def circuitAt (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles ambient :=
  UnitaryCircuit.placeAt layout ambient
    (positions control left right controlLeft controlRight leftRight)
    (dimensions ambient control left right controlLeft controlRight leftRight
      controlQubit leftQubit rightQubit) (circuit oracles)

/-- Exact target semantics holds on all selected and unselected systems jointly. -/
public theorem controlledSwap_circuitAt_matrix (oracles : OracleModel) :
    (circuitAt ambient control left right controlLeft controlRight leftRight
      controlQubit leftQubit rightQubit oracles).matrix =
      placedOperator ambient control left right controlLeft controlRight leftRight
        controlQubit leftQubit rightQubit := by
  rw [circuitAt, UnitaryCircuit.placeAt_matrix, controlledSwap_circuit_matrix]
  rfl

/-- Physical placement preserves the complete native event order. -/
public theorem controlledSwap_circuitAt_events (oracles : OracleModel) :
    (circuitAt ambient control left right controlLeft controlRight leftRight
      controlQubit leftQubit rightQubit oracles).eventTrace =
      [.gate .cnot, .gate .toffoli, .gate .cnot] := by
  rw [circuitAt, UnitaryCircuit.placeAt_eventTrace, controlledSwap_circuit_events]

/-- The actual dependency depth remains three after placement. -/
public theorem controlledSwap_circuitAt_unit_depth (oracles : OracleModel) :
    (circuitAt ambient control left right controlLeft controlRight leftRight
      controlQubit leftQubit rightQubit oracles).evaluatedEventDepth (fun _ => 1) = 3 := by
  change DepthExpr.depthEval (fun _ => 1)
    (circuitAt ambient control left right controlLeft controlRight leftRight
      controlQubit leftQubit rightQubit oracles).eventDepth = 3
  rw [circuitAt, UnitaryCircuit.placeAt_eventDepth]
  exact controlledSwap_circuit_unit_depth oracles

end

end QuantumAlg.Gate.ControlledSwap
