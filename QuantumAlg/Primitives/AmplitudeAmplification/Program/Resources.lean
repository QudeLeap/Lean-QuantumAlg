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
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
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
def stepEventPool {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    ResourcePool (.quantum AlgorithmGate.model (oracles U good)) :=
  ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .goodReflection) +
    ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .inversePreparation) +
    ZeroReflection.elementaryEventPool (oracles U good) n + ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .preparation)

/-- Initial preparation and exactly k literal source iterates. -/
def unitaryEventPool {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (oracles U good)) :=
  ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .preparation) + k • stepEventPool U good

/-- Each source call and each elementary occurrence has unit duration. -/
def unitaryDepth (n k : Nat) : Nat := 1 + k * (3 + ZeroReflection.elementaryGateCount n)

/-- The only elementary gates outside source queries implement the known reflections. -/
def unitaryGateCount (n k : Nat) : Nat := k * ZeroReflection.elementaryGateCount n

private theorem preparation_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (preparation U good k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .preparation) := by
  rw [preparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    AmplitudeAmplificationSource.Circuit.program_eventCost]
  rfl

private theorem inversePreparation_eventCost {n : Nat}
    (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (inversePreparation U good k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .inversePreparation) := by
  rw [inversePreparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    AmplitudeAmplificationSource.Circuit.program_eventCost]
  rfl

private theorem goodReflection_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n))
    (k : Nat) :
    (goodReflection U good k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles U good))
      (.oracle .goodReflection) := by
  rw [goodReflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    AmplitudeAmplificationSource.Circuit.program_eventCost]
  rfl

private theorem preparation_unitDepth {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (preparation U good k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [preparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  rfl

private theorem inversePreparation_unitDepth {n : Nat}
    (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (inversePreparation U good k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [inversePreparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  rfl

private theorem goodReflection_unitDepth {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n))
    (k : Nat) : (goodReflection U good k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [goodReflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  rfl

theorem program_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (program U good k).eventCost = unitaryEventPool U good k := by
  by_cases zero : k = 0
  · subst k
    rw [program, dif_pos rfl, preparation_eventCost]
    simp only [unitaryEventPool, zero_nsmul, add_zero]
  · simp only [program, dif_neg zero, step, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.iterate_eventCost, preparation_eventCost,
      inversePreparation_eventCost, goodReflection_eventCost,
      ZeroReflection.Workspace.reflection_eventCost]
    rfl

theorem program_unitDepth {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (program U good k).evaluatedEventDepth (fun _ => 1) = unitaryDepth n k := by
  have repeated (count : Nat)
      (body : UnitaryCircuit AlgorithmGate.model (oracles U good)
        (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout) :
      (UnitaryCircuit.iterate count body).evaluatedEventDepth (fun _ => 1) =
        count * body.evaluatedEventDepth (fun _ => 1) := rfl
  by_cases zero : k = 0
  · subst k
    rw [program, dif_pos rfl, preparation_unitDepth]
    simp only [unitaryDepth, Nat.zero_mul, Nat.add_zero]
  · simp only [program, dif_neg zero, step, UnitaryCircuit.evaluatedEventDepth_seq,
      repeated, preparation_unitDepth,
      inversePreparation_unitDepth, goodReflection_unitDepth,
      ZeroReflection.Workspace.reflection_unitDepth, unitaryDepth]
    ring

theorem program_gateCount {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (program U good k).eventCost = unitaryGateCount n k := by
  let weight : Resource.Event (.quantum AlgorithmGate.model (oracles U good)) → Nat :=
    fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (program U good k).eventCost = _
  have reflected : ResourcePool.weightedCount weight
      (ZeroReflection.elementaryEventPool (oracles U good) n) =
      ZeroReflection.elementaryGateCount n := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_gateCount (oracles U good) n)
    apply congrArg (fun assignment :
        Resource.Event (.quantum AlgorithmGate.model (oracles U good)) → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool (oracles U good) n))
    funext event
    cases event <;> rfl
  rw [program_eventCost]
  simp only [unitaryEventPool, stepEventPool, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton]
  rw [reflected]
  dsimp only [weight, unitaryGateCount]
  ring

end

end QuantumAlg.AmplitudeAmplification.Native
