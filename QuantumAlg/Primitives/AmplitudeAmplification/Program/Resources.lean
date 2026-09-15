/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Program
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace
import all QuantumAlg.Core.Base.UnitaryCircuit.IdleSuffix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Independent source counts for the actual amplification program

The formulas charge the initial source preparation and every actual iterate.
They depend only on source width and iteration count. Source-query coordinates
remain distinct from the elementary implementation of the known reflection.
-/

namespace QuantumAlg.AmplitudeAmplification.Native

noncomputable section

open AmplitudeAmplificationSource ZeroReflection.Workspace

/-- The four independent source-iterate resource terms, in execution order. -/
def stepEventPool (n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (goodReflectionEvent n) +
    ResourcePool.singleton (inversePreparationEvent n) +
    ZeroReflection.elementaryEventPool n + ResourcePool.singleton (preparationEvent n)

/-- Initial preparation and exactly k literal source iterates. -/
def unitaryEventPool (n k : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (preparationEvent n) + k • stepEventPool n

/-- Each source call and each elementary occurrence has unit duration. -/
def unitaryDepth (n k : Nat) : Nat := 1 + k * (3 + ZeroReflection.elementaryGateCount n)

/-- The only elementary gates outside source queries implement the known reflections. -/
def unitaryGateCount (n k : Nat) : Nat := k * ZeroReflection.elementaryGateCount n

private theorem preparation_eventCost {n : Nat} (U : UnitaryOperator (Qubits n)) (k : Nat) :
    (preparation U k).eventCost = ResourcePool.singleton (preparationEvent n) := by
  rw [preparation, UnitaryCircuit.idleSuffix_eventCost,
    AmplitudeAmplificationSource.Circuit.preparation_eventCost]

private theorem inversePreparation_eventCost {n : Nat}
    (U : UnitaryOperator (Qubits n)) (k : Nat) :
    (inversePreparation U k).eventCost = ResourcePool.singleton (inversePreparationEvent n) := by
  rw [inversePreparation, UnitaryCircuit.idleSuffix_eventCost,
    AmplitudeAmplificationSource.Circuit.inversePreparation_eventCost]

private theorem goodReflection_eventCost {n : Nat} (good : NormalizedVector (Qubits n))
    (k : Nat) :
    (goodReflection good k).eventCost = ResourcePool.singleton (goodReflectionEvent n) := by
  rw [goodReflection, UnitaryCircuit.idleSuffix_eventCost,
    AmplitudeAmplificationSource.Circuit.goodReflection_eventCost]

private theorem preparation_unitDepth {n : Nat} (U : UnitaryOperator (Qubits n)) (k : Nat) :
    (preparation U k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [preparation, UnitaryCircuit.idleSuffix_evaluatedEventDepth]
  rfl

private theorem inversePreparation_unitDepth {n : Nat}
    (U : UnitaryOperator (Qubits n)) (k : Nat) :
    (inversePreparation U k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [inversePreparation, UnitaryCircuit.idleSuffix_evaluatedEventDepth]
  rfl

private theorem goodReflection_unitDepth {n : Nat} (good : NormalizedVector (Qubits n))
    (k : Nat) : (goodReflection good k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [goodReflection, UnitaryCircuit.idleSuffix_evaluatedEventDepth]
  rfl

theorem program_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (program U good k).eventCost = unitaryEventPool n k := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero]
  by_cases zero : k = 0
  · subst k
    rw [body, dif_pos rfl, preparation_eventCost]
    simp only [unitaryEventPool, zero_nsmul, add_zero]
  · simp only [body, dif_neg zero, step, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.iterate_eventCost, preparation_eventCost,
      inversePreparation_eventCost, goodReflection_eventCost,
      ZeroReflection.Workspace.reflection_eventCost]
    rfl

theorem program_unitDepth {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (program U good k).evaluatedEventDepth (fun _ => 1) = unitaryDepth n k := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq]
  have finalIdentity :
      (UnitaryCircuit.identity (Qubits (totalQubits n k))
        (List.range (totalQubits n k)) List.nodup_range).evaluatedEventDepth
          (fun _ => 1) = 0 := rfl
  rw [finalIdentity, add_zero]
  by_cases zero : k = 0
  · subst k
    rw [body, dif_pos rfl, preparation_unitDepth]
    simp only [unitaryDepth, Nat.zero_mul, Nat.add_zero]
  · simp only [body, dif_neg zero, step, UnitaryCircuit.evaluatedEventDepth_seq,
      UnitaryCircuit.evaluatedEventDepth_iterate, preparation_unitDepth,
      inversePreparation_unitDepth, goodReflection_unitDepth,
      ZeroReflection.Workspace.reflection_unitDepth, unitaryDepth]
    ring

theorem program_gateCount {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (program U good k).eventCost = unitaryGateCount n k := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (program U good k).eventCost = _
  have reflected : ResourcePool.weightedCount weight (ZeroReflection.elementaryEventPool n) =
      ZeroReflection.elementaryGateCount n := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_gateCount n)
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool n))
    funext event
    cases event <;> rfl
  rw [program_eventCost]
  simp only [unitaryEventPool, stepEventPool, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton]
  rw [reflected]
  dsimp only [weight, preparationEvent, inversePreparationEvent, goodReflectionEvent,
    unitaryGateCount]
  ring

end

end QuantumAlg.AmplitudeAmplification.Native
