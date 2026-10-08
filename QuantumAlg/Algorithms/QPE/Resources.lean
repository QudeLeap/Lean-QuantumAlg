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

private theorem preparation_pool {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (preparationCode P t).Path) :
    ResourcePool.ofList ((preparationCode P t).eventTrace path) =
      t • ResourcePool.singleton (model := model P)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (UnitarySource.model P.unitary true)
    (phaseRuntimeLayout t) 2 (fun _ => rfl) BitWord.model .empty

private theorem program_pool {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    ResourcePool.ofList ((nativeProgram P t).eventTrace BitWord.model .empty) =
      (2 * t + 3 * t.choose 2) • ResourcePool.singleton (model := model P)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
      (2 * t.choose 2 + 3 * (t / 2)) • ResourcePool.singleton (model := model P)
        (.gate AlgorithmGate.Coordinate.cnot) +
      (2 ^ t - 1) • ResourcePool.singleton (model := model P)
        (.oracle UnitarySource.Coordinate.controlled) := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram P t) BitWord.model .empty,
    nativeProgram, unitaryOfEqualWires_cost (runtimeLayout t n)
      (preparedContext t n).quantumLayout (runtime_wires t n) (Native.circuit t P.unitary)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((Native.circuit t P.unitary).eventCost BitWord.model .empty) = ResourcePool.count event _
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

private theorem measurement_pool {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model P.unitary true) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model P.unitary true) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).eventTrace path) =
      t • ResourcePool.singleton (model := model P)
        (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts t n) (readouts_qubits t n),
    readouts_length]
  rfl

private theorem allocation_trace {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (allocationCode P t).Path) : (allocationCode P t).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model P) (resultContext t n) 2 t path.2

/-- Every actual path has exactly the independently specified native event pool. -/
theorem code_events {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (code P t).Path) : (code P t).resourcePool path = eventBudget P t := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool P t path.1.1]
  rfl

private theorem program_depth {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    DepthExpr.depthEval (fun _ => 1) ((nativeProgram P t).eventDepth BitWord.model .empty) =
      ((if t = 0 then 0 else 1) + (2 ^ t - 1)) +
        (t + 5 * t.choose 2 + 3 * (t / 2)) := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (Native.circuit t P.unitary).evaluatedEventDepth (fun _ => 1) = _
  exact Native.qpeNative_circuit_unit_depth t P.unitary

/-- The actual critical path satisfies the independent complete unit-duration bound. -/
theorem code_depth {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (code P t).Path) : (code P t).depth (fun _ => 1) path ≤ depthBudget t := by
  have preparation :
      DepthExpr.depthEval (fun _ => 1)
        (ZeroPreparation.eventDepth AlgorithmGate.model (UnitarySource.model P.unitary true)
          (phaseRuntimeLayout t) BitWord.model .empty) = if t = 0 then 0 else 1 :=
    ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
      (UnitarySource.model P.unitary true) (phaseRuntimeLayout t) 2 (fun _ => rfl)
      BitWord.model .empty
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (UnitarySource.model P.unitary true)
        (phaseRuntimeLayout t) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((nativeProgram P t).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model P)
        (resultContext t n) 2 t).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model P.unitary true) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).depth (fun _ => 1) path.2.1 + 1) ≤ _
  rw [preparation, MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  unfold depthBudget
  omega

/-- Every path contains exactly the original controlled-source query multiplicity. -/
theorem code_controlledUnitaryCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (code P t).Path) :
    ResourcePool.count (model := model P) (.oracle UnitarySource.Coordinate.controlled)
      ((code P t).resourcePool path) = 2 ^ t - 1 := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

/-- Exact native single-qubit count of the complete phase-estimation execution. -/
theorem qpeCode_singleQubitCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (code P t).Path) :
    ResourcePool.count (model := model P) (.gate .singleQubit)
      ((code P t).resourcePool path) = 2 * t + 3 * t.choose 2 := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

/-- Exact native CNOT count, including controlled-phase and SWAP expansions. -/
theorem qpeCode_cnotCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (code P t).Path) :
    ResourcePool.count (model := model P) (.gate .cnot)
      ((code P t).resourcePool path) = 2 * t.choose 2 + 3 * (t / 2) := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

/-- The complete native phase-estimation execution contains no Toffoli gate. -/
theorem qpeCode_toffoliCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (code P t).Path) :
    ResourcePool.count (model := model P) (.gate .toffoli)
      ((code P t).resourcePool path) = 0 := by
  rw [code_events]
  simp [eventBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]

end

end QuantumAlg.QuantumPhaseEstimation
