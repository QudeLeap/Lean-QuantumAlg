/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Reflection
import all QuantumAlg.Algorithms.QPE.Query.Ladder
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Algorithms.QPE.Readout
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Independent native resources of elementary amplitude estimation

The source grants ordinary preparation, inverse preparation and controlled
good-reflection queries. The known controlled zero reflection contributes
only its actual elementary X, H, Z, CNOT and Toffoli occurrences. Every
formula below depends on widths alone; the one actual stored sequence
supplies the equal event multiplicities and critical-path depths.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

open AmplitudeAmplificationSource

/-- Three separate source-query coordinates and the independent native S0 budget. -/
def stepEventPool (n : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (oracles n)) :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .controlledGoodReflection) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .inversePreparation) +
    ZeroReflection.controlledElementaryEventPool (oracles n) n +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .preparation)

/-- Expanded native inverse-Fourier multiplicities on the original phase register. -/
def readoutEventPool (queries : OracleModel) (t : Nat) :
    ResourcePool (.quantum AlgorithmGate.model queries) :=
  (t + 3 * t.choose 2) • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model queries) (.gate .singleQubit) +
    (2 * t.choose 2 + 3 * (t / 2)) • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model queries) (.gate .cnot)

/-- Independent full budget includes the ordinary initial preparation query. -/
def unitaryEventPool (n : Nat) (t : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (oracles n)) :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model (oracles n))
      (.oracle .preparation) +
    (t • ResourcePool.singleton (model := .quantum AlgorithmGate.model (oracles n))
      (.gate .singleQubit) +
      ((2 ^ t - 1) • stepEventPool n + readoutEventPool (oracles n) t))

/-- Independent duration of one actual source iterate, with sequential elementary S0. -/
def stepDepth (n : Nat) : Nat := 3 + ZeroReflection.controlledElementaryGateCount n

/-- Unit-duration budget retains parallel phase Hadamards and the literal source/readout order. -/
def unitaryDepth (t n : Nat) : Nat :=
  1 + ((if t = 0 then 0 else 1) +
    ((2 ^ t - 1) * stepDepth n + (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3))))

/-- Exact native critical path, with all disjoint readout SWAPs executed in parallel. -/
def unitaryCriticalPath (t n : Nat) : Nat :=
  1 + ((if t = 0 then 0 else 1) +
    ((2 ^ t - 1) * stepDepth n +
      (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3))))

/-- Parallel readout remains within the independent complete unit-duration budget. -/
lemma unitaryCriticalPath_le_unitaryDepth (t n : Nat) :
    unitaryCriticalPath t n ≤ unitaryDepth t n := by
  have reversal : (if t / 2 = 0 then 0 else 3) ≤ 3 * (t / 2) := by
    split <;> omega
  unfold unitaryCriticalPath unitaryDepth
  omega

/-- Independent elementary count excludes the three separately counted source-query families. -/
def unitaryGateCount (t n : Nat) : Nat :=
  2 * t + (2 ^ t - 1) * ZeroReflection.controlledElementaryGateCount n +
    5 * t.choose 2 + 3 * (t / 2)

lemma step_eventCost (n : Nat) {t : Nat} (stage : Fin t) :
    (step n stage).eventCost = stepEventPool n := by
  simp only [step, UnitaryCircuit.seq_eventCost, controlledGoodReflection_eventCost,
    inversePreparation_eventCost, reflection_eventCost, preparation_eventCost, stepEventPool]

lemma step_unitDepth (n : Nat) {t : Nat} (stage : Fin t) :
    (step n stage).evaluatedEventDepth (fun _ => 1) = stepDepth n := by
  simp only [step, UnitaryCircuit.evaluatedEventDepth_seq, controlledGoodReflection_unitDepth,
    inversePreparation_unitDepth, reflection_unitDepth, preparation_unitDepth, stepDepth]
  omega

lemma ladder_eventCost (n : Nat) (t : Nat) :
    (ladder n t).eventCost = (2 ^ t - 1) • stepEventPool n := by
  rw [ladder, UnitaryCircuit.indexedProduct_eventCost,
    UnitaryCircuit.identity_eventCost, zero_add]
  simp only [powerStage, UnitaryCircuit.iterate_eventCost, step_eventCost]
  rw [Finset.sum_nsmul_assoc]
  rw [QuantumPhaseEstimation.Native.sum_stage_queries]

lemma ladder_unitDepth (n : Nat) (t : Nat) :
    (ladder n t).evaluatedEventDepth (fun _ => 1) = (2 ^ t - 1) * stepDepth n := by
  rw [ladder]
  change 0 + ∑ stage : Fin t, 2 ^ stage.val *
    (step n stage).evaluatedEventDepth (fun _ => 1) = _
  simp only [zero_add, step_unitDepth]
  rw [← Finset.sum_mul, QuantumPhaseEstimation.Native.sum_stage_queries]

private lemma castCircuit_cost (queries : OracleModel) {left right : Nat}
    (same : left = right) (body : UnitaryCircuit AlgorithmGate.model queries
      (QuantumSignature.qubits left).canonicalPlacement.layout) :
    (castCircuit queries same body).eventCost = body.eventCost := by
  cases same
  rfl

private lemma castCircuit_depth (queries : OracleModel) {left right : Nat}
    (same : left = right) (body : UnitaryCircuit AlgorithmGate.model queries
      (QuantumSignature.qubits left).canonicalPlacement.layout) :
    (castCircuit queries same body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) := by
  cases same
  rfl

private lemma phaseHadamards_eventCost (queries : OracleModel) (t n : Nat) :
    (phaseHadamards queries t n).eventCost = t • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model queries) (.gate .singleQubit) := by
  rw [phaseHadamards, castCircuit_cost, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
  exact Gate.HadamardLayer.hadamardLayer_circuit_eventCost queries t

private lemma phaseReadout_eventCost (queries : OracleModel) (t n : Nat) :
    (phaseReadout queries t n).eventCost = readoutEventPool queries t := by
  rw [phaseReadout, castCircuit_cost, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (qpeReadoutCircuit queries t).eventCost =
    ResourcePool.count event (readoutEventPool queries t)
  rw [qpeReadout_native_event_count]
  simp only [readoutEventPool, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

private lemma phaseHadamards_unitDepth (queries : OracleModel) (t n : Nat) :
    (phaseHadamards queries t n).evaluatedEventDepth (fun _ => 1) =
      if t = 0 then 0 else 1 := by
  rw [phaseHadamards, castCircuit_depth, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth queries t

private lemma phaseReadout_unitDepth (queries : OracleModel) (t n : Nat) :
    (phaseReadout queries t n).evaluatedEventDepth (fun _ => 1) =
      t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3) := by
  rw [phaseReadout, castCircuit_depth, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact qpeReadout_native_unit_depth queries t

/-- Every count is an equality on the single actual unitary sequence. -/
lemma program_eventCost (n : Nat) (t : Nat) :
    (program n t).eventCost = unitaryEventPool n t := by
  simp only [program, UnitaryCircuit.seq_eventCost, preparation_eventCost,
    phaseHadamards_eventCost, ladder_eventCost, phaseReadout_eventCost, unitaryEventPool]

/-- Exact critical-path depth includes the original phase readout and every source occurrence. -/
lemma program_unitDepth (n : Nat) (t : Nat) :
    (program n t).evaluatedEventDepth (fun _ => 1) = unitaryCriticalPath t n := by
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq, preparation_unitDepth,
    phaseHadamards_unitDepth, ladder_unitDepth, phaseReadout_unitDepth, unitaryCriticalPath]

end

end QuantumAlg.AmplitudeEstimation.Elementary
