/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Actual elementary and source-query counts for amplitude estimation

The independent native ledger counts only elementary leaves in the gate
projection. Ordinary preparation, its inverse and controlled good reflection
retain separate source coordinates, including the initial preparation call.
Every equality holds for the actual program at all phase and source widths,
including the total-definition branch with one additional work system.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

open AmplitudeAmplificationSource

noncomputable section

/-- The exact query ledger separates initial preparation from the three per-step calls. -/
theorem program_oracleCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (coordinate : AmplitudeAmplificationSource.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles U good))
        (.oracle coordinate) (program t U good).eventCost =
      (if coordinate = .preparation then 1 else 0) +
        (2 ^ t - 1) * (if coordinate = .goodReflection then 0 else 1) := by
  rw [program_eventCost]
  cases coordinate <;> rcases n with _ | _ | _ | n <;>
    simp [unitaryEventPool, stepEventPool, readoutEventPool,
      ZeroReflection.controlledElementaryEventPool,
      ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Native gates exclude every separately granted oracle query. -/
theorem program_gateCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (program t U good).eventCost = unitaryGateCount t n := by
  rw [program_eventCost]
  rcases n with _ | _ | _ | n <;>
    simp [unitaryEventPool, stepEventPool, readoutEventPool, unitaryGateCount,
      ZeroReflection.controlledElementaryEventPool, ZeroReflection.controlledElementaryGateCount,
      ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
      ResourcePool.weightedCount_singleton] <;> ring

/-- The initial ordinary preparation remains present even with no phase-estimation stage. -/
theorem program_preparationCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .preparation) (program t U good).eventCost = (2 ^ t - 1) + 1 := by
  simpa [Nat.add_comm] using program_oracleCount t U good .preparation

/-- Every actual source step contains one ordinary inverse-preparation query. -/
theorem program_inversePreparationCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .inversePreparation) (program t U good).eventCost = 2 ^ t - 1 := by
  simpa using program_oracleCount t U good .inversePreparation

/-- Every actual source step contains one explicitly granted controlled recognizer. -/
theorem program_controlledGoodReflectionCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .controlledGoodReflection) (program t U good).eventCost = 2 ^ t - 1 := by
  simpa using program_oracleCount t U good .controlledGoodReflection

/-- The ordinary recognizer coordinate is not used in this controlled ladder. -/
theorem program_goodReflectionCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .goodReflection) (program t U good).eventCost = 0 := by
  simpa using program_oracleCount t U good .goodReflection

end

end QuantumAlg.AmplitudeEstimation.Elementary
