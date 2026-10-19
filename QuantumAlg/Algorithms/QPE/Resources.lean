/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Algorithms.QPE.Circuit.Resources
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Exact events and dependency depth of the complete native QPE execution

Only the owned phase prefix is zero-prepared. Actual native gates, every
controlled source query, each ordered Z write and the final packing instruction
contribute to the independently specified resource pool and dependency depth.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

private lemma preparation_pool (n : Nat) (t : Nat)
    (path : (preparationCode n t).Path) :
    ResourcePool.ofList ((preparationCode n t).eventTrace path) =
      t • ResourcePool.singleton (model := model n)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (UnitarySource.model n true)
    (phaseRuntimeLayout t) 2 (fun _ => rfl) BitWord.model .empty

private lemma program_pool (n : Nat) (t : Nat) :
    ResourcePool.ofList ((nativeProgram n t).eventTrace BitWord.model .empty) =
      (2 * t + 3 * t.choose 2) • ResourcePool.singleton (model := model n)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
      (2 * t.choose 2 + 3 * (t / 2)) • ResourcePool.singleton (model := model n)
        (.gate AlgorithmGate.Coordinate.cnot) +
      (2 ^ t - 1) • ResourcePool.singleton (model := model n)
        (.oracle UnitarySource.Coordinate.controlled) := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram n t) BitWord.model .empty,
    nativeProgram, unitaryOfEqualWires_cost (runtimeLayout t n)
      (preparedContext t n).quantumLayout (runtime_wires t n) (Native.circuit t n)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((Native.circuit t n).eventCost BitWord.model .empty) = ResourcePool.count event _
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      change AlgorithmGate.Coordinate at coordinate
      cases coordinate <;>
        simp [Native.qpeNative_circuit_event_count, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | oracle coordinate =>
      change UnitarySource.Coordinate at coordinate
      cases coordinate <;>
        simp [Native.qpeNative_circuit_event_count, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | _ => simp [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

private lemma measurement_pool (n : Nat) (t : Nat)
    (path : (Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model n true) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model n true) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).eventTrace path) =
      t • ResourcePool.singleton (model := model n)
        (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts t n) (readouts_qubits t n),
    readouts_length]
  rfl

private lemma allocation_trace (n : Nat) (t : Nat)
    (path : (allocationCode n t).Path) : (allocationCode n t).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model n) (resultContext t n) 2 t path.2

/-- Every actual path has exactly the independently specified native event pool. -/
lemma code_events (n : Nat) (t : Nat)
    (path : (code n t).Path) : (code n t).resourcePool path = eventBudget n t := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool n t path.1.1]
  rfl

private lemma program_depth (n : Nat) (t : Nat) :
    DepthExpr.depthEval (fun _ => 1) ((nativeProgram n t).eventDepth BitWord.model .empty) =
      ((if t = 0 then 0 else 1) + (2 ^ t - 1)) +
        (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3)) := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (Native.circuit t n).evaluatedEventDepth (fun _ => 1) = _
  exact Native.qpeNative_circuit_unit_depth t n

/-- The actual critical path satisfies the independent complete unit-duration bound. -/
lemma code_depth (n : Nat) (t : Nat)
    (path : (code n t).Path) : (code n t).depth (fun _ => 1) path ≤ depthBudget t := by
  have preparation :
      DepthExpr.depthEval (fun _ => 1)
        (ZeroPreparation.eventDepth AlgorithmGate.model (UnitarySource.model n true)
          (phaseRuntimeLayout t) BitWord.model .empty) = if t = 0 then 0 else 1 :=
    ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
      (UnitarySource.model n true) (phaseRuntimeLayout t) 2 (fun _ => rfl)
      BitWord.model .empty
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (UnitarySource.model n true)
        (phaseRuntimeLayout t) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((nativeProgram n t).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model n)
        (resultContext t n) 2 t).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model n true) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).depth (fun _ => 1) path.2.1 + 1) ≤ _
  rw [preparation, MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  have reversal : (if t / 2 = 0 then 0 else 3) ≤ 3 * (t / 2) := by
    split <;> omega
  unfold depthBudget
  omega

/-- Every path contains exactly the original controlled-source query multiplicity. -/
lemma code_controlledUnitaryCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.oracle UnitarySource.Coordinate.controlled)
      ((code n t).resourcePool path) = 2 ^ t - 1 := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

/-- Exact native single-qubit count of the complete phase-estimation execution. -/
lemma qpeCode_singleQubitCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.gate .singleQubit)
      ((code n t).resourcePool path) = 2 * t + 3 * t.choose 2 := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

/-- Exact native CNOT count, including controlled-phase and SWAP expansions. -/
lemma qpeCode_cnotCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.gate .cnot)
      ((code n t).resourcePool path) = 2 * t.choose 2 + 3 * (t / 2) := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

/-- The complete native phase-estimation execution contains no Toffoli gate. -/
lemma qpeCode_toffoliCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.gate .toffoli)
      ((code n t).resourcePool path) = 0 := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

end

end QuantumAlg.QuantumPhaseEstimation
