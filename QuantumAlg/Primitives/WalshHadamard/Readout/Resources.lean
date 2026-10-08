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

private theorem preparation_pool {n : Nat} (f : WalshHadamard.Oracle n)
    (path : (preparationCode f).Path) :
    ResourcePool.ofList ((preparationCode f).eventTrace path) =
      (n + 1) • ResourcePool.singleton (model := model f)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model (XorOracle.model f)
    (runtimeLayout n) 2 (fun _ => rfl) BitWord.model .empty

private theorem program_pool {n : Nat} (f : WalshHadamard.Oracle n) :
    ResourcePool.ofList ((program f).eventTrace BitWord.model .empty) =
      (2 * n + 2) • ResourcePool.singleton (model := model f)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
        ResourcePool.singleton (model := model f)
        (.oracle XorOracle.Coordinate.xor) := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (program f) BitWord.model .empty, program,
    unitaryOfEqualWires_cost (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) (Native.zeroInputProgram f)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((Native.zeroInputProgram f).eventCost BitWord.model .empty) = ResourcePool.count event _
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

private theorem measurement_pool {n : Nat} (f : WalshHadamard.Oracle n)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := XorOracle.model f) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := XorOracle.model f) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n)).eventTrace path) =
      n • ResourcePool.singleton (model := model f)
        (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts n) (readouts_qubits n),
    readouts_length]
  rfl

private theorem allocation_trace {n : Nat} (f : WalshHadamard.Oracle n)
    (path : (allocationCode f).Path) : (allocationCode f).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model f) (resultContext n) 2 n path.2

/-- Literal native counts of the actual complete program, on every execution path. -/
theorem code_events {n : Nat} (f : WalshHadamard.Oracle n) (path : (code f).Path) :
    (code f).resourcePool path =
      (n + 1) • ResourcePool.singleton (model := model f)
        (.preparation (2 : ℕ+)) +
      ((2 * n + 2) • ResourcePool.singleton (model := model f)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
        ResourcePool.singleton (model := model f)
        (.oracle XorOracle.Coordinate.xor)) +
      (n • ResourcePool.singleton (model := model f)
        (.measurement (2 : ℕ+)) +
        ResourcePool.singleton (model := model f)
        (.classicalOperation (Resource.ClassicalOpLabel.nominalEncoding (.packFiniteBits n)))) := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool f path.1.1]
  rfl

private theorem program_depth {n : Nat} (f : WalshHadamard.Oracle n) :
    DepthExpr.depthEval (fun _ => 1) ((program f).eventDepth BitWord.model .empty) =
      if n = 0 then 3 else 4 := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (Native.zeroInputProgram f).evaluatedEventDepth (fun _ => 1) = _
  exact Native.walshNative_zeroInputProgram_unit_depth f

/-- Preparation, every sequential Z read and packing contribute to the actual total depth. -/
theorem code_depth {n : Nat} (f : WalshHadamard.Oracle n) (path : (code f).Path) :
    (code f).depth (fun _ => 1) path = 1 + (if n = 0 then 3 else 4) + n + 1 := by
  have preparation :
      DepthExpr.depthEval (fun _ => 1)
        (ZeroPreparation.eventDepth AlgorithmGate.model (XorOracle.model f)
          (runtimeLayout n) BitWord.model .empty) = 1 := by
    rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
      (XorOracle.model f) (runtimeLayout n) 2 (fun _ => rfl) BitWord.model .empty]
    simp
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (XorOracle.model f)
        (runtimeLayout n) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((program f).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model f)
        (resultContext n) 2 n).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := XorOracle.model f) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [preparation, MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  omega

end

end QuantumAlg.WalshHadamard.Readout
