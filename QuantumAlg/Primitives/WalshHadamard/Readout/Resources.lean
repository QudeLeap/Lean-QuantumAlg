/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Initialization
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Exact native events and depth of the complete Walsh readout

Fixed zero preparation emits one event per real qubit. The target X is an
actual single-qubit gate. The same runtime then executes both Hadamard layers,
one granted XOR query, every ordered Z write and the charged bit packing.
No measurement occurs at width zero, while X and packing still execute.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

private lemma preparation_pool (n : Nat)
    (path : (preparationCode n).Path) :
    ResourcePool.ofList ((preparationCode n).eventTrace path) =
      (n + 1) • ResourcePool.singleton (model := model n)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model (XorOracle.model n)
    (runtimeLayout n) 2 (fun _ => rfl) BitWord.model .empty

private lemma program_pool (n : Nat) :
    ResourcePool.ofList ((program n).eventTrace BitWord.model .empty) =
      (2 * n + 2) • ResourcePool.singleton (model := model n)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
        ResourcePool.singleton (model := model n)
        (.oracle XorOracle.Coordinate.xor) := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (program n) BitWord.model .empty, program,
    unitaryOfEqualWires_cost (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) (Native.zeroInputProgram n)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((Native.zeroInputProgram n).eventCost BitWord.model .empty) = ResourcePool.count event _
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      change AlgorithmGate.Coordinate at coordinate
      cases coordinate <;>
        simp [Native.walshNative_zeroInputProgram_eventCost, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | oracle coordinate =>
      change XorOracle.Coordinate at coordinate
      cases coordinate
      simp [Native.walshNative_zeroInputProgram_eventCost, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | _ => simp [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

private lemma measurement_pool (n : Nat)
    (path : (Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := XorOracle.model n) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := XorOracle.model n) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n)).eventTrace path) =
      n • ResourcePool.singleton (model := model n)
        (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts n) (readouts_qubits n),
    readouts_length]
  rfl

private lemma allocation_trace (n : Nat)
    (path : (allocationCode n).Path) : (allocationCode n).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model n) (resultContext n) 2 n path.2

/-- Literal native counts of the actual complete program, on every execution path. -/
lemma code_events (n : Nat) (path : (code n).Path) :
    (code n).resourcePool path =
      (n + 1) • ResourcePool.singleton (model := model n)
        (.preparation (2 : ℕ+)) +
      ((2 * n + 2) • ResourcePool.singleton (model := model n)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
        ResourcePool.singleton (model := model n)
        (.oracle XorOracle.Coordinate.xor)) +
      (n • ResourcePool.singleton (model := model n)
        (.measurement (2 : ℕ+)) +
        ResourcePool.singleton (model := model n)
        (.classicalOperation (Resource.ClassicalOpLabel.nominalEncoding (.packFiniteBits n)))) := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool n path.1.1]
  rfl

private lemma program_depth (n : Nat) :
    DepthExpr.depthEval (fun _ => 1) ((program n).eventDepth BitWord.model .empty) =
      if n = 0 then 3 else 4 := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (Native.zeroInputProgram n).evaluatedEventDepth (fun _ => 1) = _
  exact Native.walshNative_zeroInputProgram_unit_depth n

/-- Preparation, every sequential Z read and packing contribute to the actual total depth. -/
lemma code_depth (n : Nat) (path : (code n).Path) :
    (code n).depth (fun _ => 1) path = 1 + (if n = 0 then 3 else 4) + n + 1 := by
  have preparation :
      DepthExpr.depthEval (fun _ => 1)
        (ZeroPreparation.eventDepth AlgorithmGate.model (XorOracle.model n)
          (runtimeLayout n) BitWord.model .empty) = 1 := by
    rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
      (XorOracle.model n) (runtimeLayout n) 2 (fun _ => rfl) BitWord.model .empty]
    simp
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (XorOracle.model n)
        (runtimeLayout n) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((program n).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model n)
        (resultContext n) 2 n).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := XorOracle.model n) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [preparation, MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  omega

end

end QuantumAlg.WalshHadamard.Readout
