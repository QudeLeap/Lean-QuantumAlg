/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Actual source-sample event budget

The independently specified coordinates count all prepared qubits, the
expanded phase/readout native gates, the one declared source query, each Z
write, and the retained-word packing instruction. The equality below observes
each complete execution path, including the zero-width boundary.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native

noncomputable section

open QuantumAlg.Execution

/-- Independent unitary coordinates for the source word's original widths. -/
public def unitaryBudget {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) : ResourcePool (model access) :=
  (2 * t + 3 * t.choose 2) • ResourcePool.singleton (model := model access)
      (.gate AlgorithmGate.Coordinate.singleQubit) +
    (2 * t.choose 2 + 3 * (t / 2)) • ResourcePool.singleton (model := model access)
      (.gate AlgorithmGate.Coordinate.cnot) +
    ResourcePool.singleton (model := model access)
      (.oracle UnitarySource.Coordinate.ordinary)

/-- Independent full-sample budget, including storage-producing operations. -/
public def eventBudget {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) : ResourcePool (model access) :=
  (t + width) • ResourcePool.singleton (model := model access)
      (.preparation (2 : ℕ+)) +
    unitaryBudget access +
      (t • ResourcePool.singleton (model := model access) (.measurement (2 : ℕ+)) +
        ResourcePool.singleton (model := model access)
          (.classicalOperation (.nominalEncoding (.packFiniteBits t))))

private theorem preparation_pool {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (preparationCode access).Path) :
    ResourcePool.ofList ((preparationCode access).eventTrace path) =
      (t + width) • ResourcePool.singleton (model := model access)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (OrderFinding.Native.sourceModel access) (runtimeLayout t width)
    2 (fun _ => rfl) BitWord.model .empty

private theorem program_pool {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    ResourcePool.ofList ((nativeProgram access).eventTrace BitWord.model .empty) =
      unitaryBudget access := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram access) BitWord.model .empty,
    nativeProgram, Execution.unitaryOfEqualWires_cost (runtimeLayout t width)
      (preparedContext t width).quantumLayout (prepared_wires t width)
      (OrderFinding.Native.circuit access)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((OrderFinding.Native.circuit access).eventCost BitWord.model .empty) =
      ResourcePool.count event (unitaryBudget access)
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      cases coordinate <;>
        simp [OrderFinding.Native.circuit_event_count, unitaryBudget,
          ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | oracle coordinate =>
      cases coordinate <;>
        simp [OrderFinding.Native.circuit_event_count, unitaryBudget,
          ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | _ =>
      simp [unitaryBudget, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton]

private theorem measurement_pool {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel access)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts t width)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel access)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts t width)).eventTrace path) =
      t • ResourcePool.singleton (model := model access) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts t width)
      (by
        intro item present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact phaseWire_dimension t width index),
    readouts, List.length_ofFn]
  rfl

private theorem allocation_trace {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (allocationCode access).Path) :
    (allocationCode access).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model access)
    (resultContext t width) 2 t path.2

/-- Every actual full sample path has precisely the independent event budget. -/
public theorem code_events {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    (code access).resourcePool path = eventBudget access := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil,
    ResourcePool.ofList_append, program_pool, measurement_pool]
  rw [preparation_pool access path.1.1]
  rfl

/-- The complete stored sample makes exactly one granted modular-exponentiation call. -/
public theorem code_modExpCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code access).resourcePool path) = 1 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Native one-qubit count includes phase preparation and inverse Fourier expansion. -/
public theorem code_singleQubitCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := model access) (.gate .singleQubit)
      ((code access).resourcePool path) = 2 * t + 3 * t.choose 2 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Native CNOT count includes controlled phases and each physical SWAP expansion. -/
public theorem code_cnotCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := model access) (.gate .cnot)
      ((code access).resourcePool path) = 2 * t.choose 2 + 3 * (t / 2) := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- The source sampler uses no native Toffoli outside the sealed query. -/
public theorem code_toffoliCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := model access) (.gate .toffoli)
      ((code access).resourcePool path) = 0 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Every original phase wire is measured once into an actual result cell. -/
public theorem code_measurementCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := model access) (.measurement (2 : ℕ+))
      ((code access).resourcePool path) = t := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- One closed bit-packing instruction writes the retained phase word. -/
public theorem code_packCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := model access)
      (.classicalOperation (.nominalEncoding (.packFiniteBits t)))
      ((code access).resourcePool path) = 1 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.OrderFinding.Sampling.Native
