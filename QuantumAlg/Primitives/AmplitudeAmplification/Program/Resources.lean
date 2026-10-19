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
def stepEventPool (n : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (oracles n)) :=
  ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .goodReflection) +
    ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .inversePreparation) +
    ZeroReflection.elementaryEventPool (oracles n) n + ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .preparation)

/-- Initial preparation and exactly k literal source iterates. -/
def unitaryEventPool (n : Nat) (k : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (oracles n)) :=
  ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .preparation) + k • stepEventPool n

/-- Each source call and each elementary occurrence has unit duration. -/
def unitaryDepth (n k : Nat) : Nat := 1 + k * (3 + ZeroReflection.elementaryGateCount n)

/-- The only elementary gates outside source queries implement the known reflections. -/
def unitaryGateCount (n k : Nat) : Nat := k * ZeroReflection.elementaryGateCount n

private lemma preparation_eventCost (n : Nat) (k : Nat) :
    (preparation n k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .preparation) := by
  rw [preparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    AmplitudeAmplificationSource.Circuit.program_eventCost]
  rfl

private lemma inversePreparation_eventCost (n : Nat) (k : Nat) :
    (inversePreparation n k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .inversePreparation) := by
  rw [inversePreparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    AmplitudeAmplificationSource.Circuit.program_eventCost]
  rfl

private lemma goodReflection_eventCost (n : Nat)
    (k : Nat) :
    (goodReflection n k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .goodReflection) := by
  rw [goodReflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    AmplitudeAmplificationSource.Circuit.program_eventCost]
  rfl

private lemma preparation_unitDepth (n : Nat) (k : Nat) :
    (preparation n k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [preparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  rfl

private lemma inversePreparation_unitDepth (n : Nat) (k : Nat) :
    (inversePreparation n k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [inversePreparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  rfl

private lemma goodReflection_unitDepth (n : Nat)
    (k : Nat) : (goodReflection n k).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [goodReflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  rfl

lemma program_eventCost (n : Nat) (k : Nat) :
    (program n k).eventCost = unitaryEventPool n k := by
  by_cases zero : k = 0
  · subst k
    rw [program, dif_pos rfl, preparation_eventCost]
    simp only [unitaryEventPool, zero_nsmul, add_zero]
  · simp only [program, dif_neg zero, step, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.iterate_eventCost, preparation_eventCost,
      inversePreparation_eventCost, goodReflection_eventCost,
      ZeroReflection.Workspace.reflection_eventCost]
    rfl

lemma program_unitDepth (n : Nat) (k : Nat) :
    (program n k).evaluatedEventDepth (fun _ => 1) = unitaryDepth n k := by
  have repeated (count : Nat)
      (body : UnitaryCircuit AlgorithmGate.model (oracles n)
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

lemma program_gateCount (n : Nat) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (program n k).eventCost = unitaryGateCount n k := by
  let weight : Resource.Event (.quantum AlgorithmGate.model (oracles n)) → Nat :=
    fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (program n k).eventCost = _
  have reflected : ResourcePool.weightedCount weight
      (ZeroReflection.elementaryEventPool (oracles n) n) =
      ZeroReflection.elementaryGateCount n := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_gateCount (oracles n) n)
    apply congrArg (fun assignment :
        Resource.Event (.quantum AlgorithmGate.model (oracles n)) → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool (oracles n) n))
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
