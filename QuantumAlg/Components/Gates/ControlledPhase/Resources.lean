/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Native counts of the complete controlled-phase word

All counts are projections of the same retained five-gate implementation.
The descriptive macro introduces no extra gate and grants no oracle access.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The selected implementation contains exactly three native one-qubit occurrences. -/
public lemma controlledPhase_singleQubit_count (oracles : OracleModel) (angle : Real) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (circuit oracles angle).eventCost = 3 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, controlledPhase_circuit_events,
    ResourcePool.count_ofList]
  simp

/-- The selected implementation contains exactly two native CNOT occurrences. -/
public lemma controlledPhase_cnot_count (oracles : OracleModel) (angle : Real) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) (circuit
      oracles angle).eventCost = 2 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, controlledPhase_circuit_events,
    ResourcePool.count_ofList]
  simp

/-- The selected implementation uses no Toffoli occurrence. -/
public lemma controlledPhase_toffoli_count (oracles : OracleModel) (angle : Real) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli) (circuit
      oracles angle).eventCost = 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, controlledPhase_circuit_events,
    ResourcePool.count_ofList]
  simp

/-- Every declared oracle coordinate has zero queries in this implementation. -/
public lemma controlledPhase_oracle_count (oracles : OracleModel) (angle : Real)
    (coordinate : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.oracle coordinate)
      (circuit oracles angle).eventCost = 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, controlledPhase_circuit_events,
    ResourcePool.count_ofList]
  simp

end

end QuantumAlg.Gate.ControlledPhase
