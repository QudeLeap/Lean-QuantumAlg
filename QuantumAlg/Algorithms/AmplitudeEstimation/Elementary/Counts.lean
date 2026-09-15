/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Core.Base.Accounting.Control
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

private theorem reflection_quantumSubroutineCount (n : Nat)
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (ZeroReflection.controlledElementaryEventPool n) = 0 := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | extra + 3 =>
      simp only [ZeroReflection.controlledElementaryEventPool,
        ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]
      simp

/-- The full elementary program contains only the three source-granted query families. -/
theorem program_quantumSubroutineCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) (program t U good).eventCost =
      (if preparationEvent n = .quantumSubroutine label then 1 else 0) +
        (2 ^ t - 1) *
          ((if (goodReflectionEvent n).controlForDimension 2 =
              .quantumSubroutine label then 1 else 0) +
            (if inversePreparationEvent n = .quantumSubroutine label then 1 else 0) +
            (if preparationEvent n = .quantumSubroutine label then 1 else 0)) := by
  rw [program_eventCost]
  simp only [unitaryEventPool, stepEventPool, readoutEventPool,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton,
    reflection_quantumSubroutineCount]
  simp

/-- The actual elementary gate total follows from its native event pool. -/
theorem program_gateCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (program t U good).eventCost = unitaryGateCount t n := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (program t U good).eventCost = _
  have reflected : ResourcePool.weightedCount weight
      (ZeroReflection.controlledElementaryEventPool n) =
        ZeroReflection.controlledElementaryGateCount n := by
    refine Eq.trans ?_ (ZeroReflection.controlledElementaryEventPool_gateCount n)
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.controlledElementaryEventPool n))
    funext event
    cases event <;> rfl
  rw [program_eventCost]
  simp only [unitaryEventPool, stepEventPool, readoutEventPool, unitaryGateCount,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton]
  rw [reflected]
  dsimp only [weight, preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions]
  ring

/-- The initial source preparation is included in the exact `L + 1` count. -/
theorem program_preparationCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count (preparationEvent n) (program t U good).eventCost =
      (2 ^ t - 1) + 1 := by
  have count := program_quantumSubroutineCount t U good (preparationLabel n).quantum
  simpa [preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
    Resource.QuantumSubroutineLabel.controlForDimensions,
    Resource.SubroutineLabel.quantum, preparationLabel, inversePreparationLabel,
    Nat.add_comm] using count

/-- Every ladder call contains exactly one ordinary inverse query. -/
theorem program_inversePreparationCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count (inversePreparationEvent n) (program t U good).eventCost =
      2 ^ t - 1 := by
  have count := program_quantumSubroutineCount t U good (inversePreparationLabel n).quantum
  simpa [preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
    Resource.QuantumSubroutineLabel.controlForDimensions,
    Resource.SubroutineLabel.quantum, preparationLabel, inversePreparationLabel] using count

/-- The source's good-reflection capability is queried once per controlled step. -/
theorem program_controlledGoodReflectionCount {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    ResourcePool.count ((goodReflectionEvent n).controlForDimension 2)
        (program t U good).eventCost = 2 ^ t - 1 := by
  have count := program_quantumSubroutineCount t U good
    ((goodReflectionLabel n).quantum.controlForDimension 2)
  simpa [preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
    Resource.QuantumSubroutineLabel.controlForDimension,
    Resource.QuantumSubroutineLabel.controlForDimensions,
    Resource.SubroutineLabel.quantum] using count


end

end QuantumAlg.AmplitudeEstimation.Elementary
