/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap
import all QuantumAlg.Components.Gates.Swap
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# The complete native SWAP on selected ambient qubits

Left and right are distinct physical positions of dimension two. The
complete three-CNOT word is relocated there; every other ambient system keeps
its original dimension and state. No native SWAP token is introduced.
-/

namespace QuantumAlg.Gate.Swap

noncomputable section

variable {count : Nat} (ambient : QuantumLayout count)
variable (left right : Fin count) (distinct : left ≠ right)
variable (leftQubit : (ambient.wire left).dimension = 2)
variable (rightQubit : (ambient.wire right).dimension = 2)

private def positions : Fin 2 ↪ Fin count where
  toFun := ![left, right]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

include leftQubit rightQubit in
private theorem dimensions (index : Fin 2) :
    (layout.wire index).dimension =
      (ambient.wire (positions left right distinct index)).dimension := by
  fin_cases index
  · exact leftQubit.symm
  · exact rightQubit.symm

/-- Place the independent exact SWAP target on the two requested physical wires. -/
public def placedOperator : UnitaryOperator ambient.register :=
  UnitaryCircuit.operatorAt layout ambient (positions left right distinct)
    (dimensions ambient left right distinct leftQubit rightQubit) operator

/-- Run the entire native expansion at the requested left and right positions. -/
public def circuitAt (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles ambient :=
  UnitaryCircuit.placeAt layout ambient (positions left right distinct)
    (dimensions ambient left right distinct leftQubit rightQubit) (circuit oracles)

/-- The physically placed implementation retains the exact SWAP on every input. -/
public theorem swap_circuitAt_matrix (oracles : OracleModel) :
    (circuitAt ambient left right distinct leftQubit rightQubit oracles).matrix =
      placedOperator ambient left right distinct leftQubit rightQubit := by
  rw [circuitAt, UnitaryCircuit.placeAt_matrix, swap_circuit_matrix]
  rfl

/-- Placement retains all three actual native occurrences in their original order. -/
public theorem swap_circuitAt_events (oracles : OracleModel) :
    (circuitAt ambient left right distinct leftQubit rightQubit oracles).eventTrace =
      [.gate .cnot, .gate .cnot, .gate .cnot] := by
  rw [circuitAt, UnitaryCircuit.placeAt_eventTrace, swap_circuit_events]

/-- The same serial implementation has depth three on every dimension-correct ambient layout. -/
public theorem swap_circuitAt_unit_depth (oracles : OracleModel) :
    UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
      (circuitAt ambient left right distinct leftQubit rightQubit oracles) = 3 := by
  change DepthExpr.depthEval (fun _ => 1)
    (circuitAt ambient left right distinct leftQubit rightQubit oracles).eventDepth =
      3
  rw [circuitAt, UnitaryCircuit.placeAt_eventDepth]
  exact swap_circuit_unit_depth oracles

end

end QuantumAlg.Gate.Swap
