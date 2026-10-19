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
lemma program_oracleCount (n : Nat) (t : Nat)
    (coordinate : AmplitudeAmplificationSource.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles n))
        (.oracle coordinate) (program n t).eventCost =
      (if coordinate = .preparation then 1 else 0) +
        (2 ^ t - 1) * (if coordinate = .goodReflection then 0 else 1) := by
  rw [program_eventCost]
  cases coordinate <;> rcases n with _ | _ | _ | n <;>
    simp [unitaryEventPool, stepEventPool, readoutEventPool,
      ZeroReflection.controlledElementaryEventPool,
      ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Native gates exclude every separately granted oracle query. -/
lemma program_gateCount (n : Nat) (t : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (program n t).eventCost = unitaryGateCount t n := by
  rw [program_eventCost]
  rcases n with _ | _ | _ | n <;>
    simp [unitaryEventPool, stepEventPool, readoutEventPool, unitaryGateCount,
      ZeroReflection.controlledElementaryEventPool, ZeroReflection.controlledElementaryGateCount,
      ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
      ResourcePool.weightedCount_singleton] <;> ring

/-- The initial ordinary preparation remains present even with no phase-estimation stage. -/
lemma program_preparationCount (n : Nat) (t : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .preparation) (program n t).eventCost = (2 ^ t - 1) + 1 := by
  simpa [Nat.add_comm] using program_oracleCount n t .preparation

/-- Every actual source step contains one ordinary inverse-preparation query. -/
lemma program_inversePreparationCount (n : Nat) (t : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .inversePreparation) (program n t).eventCost = 2 ^ t - 1 := by
  simpa using program_oracleCount n t .inversePreparation

/-- Every actual source step contains one explicitly granted controlled recognizer. -/
lemma program_controlledGoodReflectionCount (n : Nat) (t : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .controlledGoodReflection) (program n t).eventCost = 2 ^ t - 1 := by
  simpa using program_oracleCount n t .controlledGoodReflection

/-- The ordinary recognizer coordinate is not used in this controlled ladder. -/
lemma program_goodReflectionCount (n : Nat) (t : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .goodReflection) (program n t).eventCost = 0 := by
  simpa using program_oracleCount n t .goodReflection

end

end QuantumAlg.AmplitudeEstimation.Elementary
