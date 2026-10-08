/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Resources
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Event budget with an existing classical input

The input frame contributes no new event. Every path prepares the fresh
quantum block, executes the declared source word, writes each phase bit and
packs the retained word. The budget is the same independent expression as
for the empty-input sample.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private theorem preparation_pool {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (preparationCode ctx noQuantum access).Path) :
    ResourcePool.ofList ((preparationCode ctx noQuantum access).eventTrace path) =
      (t + width) • ResourcePool.singleton (model := model access)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (OrderFinding.Native.sourceModel access) (Sampling.Native.runtimeLayout t width)
    2 (fun _ => rfl) BitWord.model .empty

private theorem program_pool {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    ResourcePool.ofList
      ((nativeProgram ctx noQuantum access).eventTrace BitWord.model .empty) =
      Sampling.Native.unitaryBudget access := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost
      (nativeProgram ctx noQuantum access) BitWord.model .empty,
    nativeProgram, Execution.unitaryOfEqualWires_cost (Sampling.Native.runtimeLayout t width)
      (preparedContext ctx noQuantum t width).quantumLayout
      (prepared_wires ctx noQuantum t width) (OrderFinding.Native.circuit access)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((OrderFinding.Native.circuit access).eventCost BitWord.model .empty) =
      ResourcePool.count event (Sampling.Native.unitaryBudget access)
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      cases coordinate <;>
        simp [OrderFinding.Native.circuit_event_count, Sampling.Native.unitaryBudget,
          ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | oracle coordinate =>
      cases coordinate <;>
        simp [OrderFinding.Native.circuit_event_count, Sampling.Native.unitaryBudget,
          ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | _ =>
      simp [Sampling.Native.unitaryBudget, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton]

private theorem measurement_pool {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel access)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts ctx noQuantum t width)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel access)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts ctx noQuantum t width)).eventTrace path) =
      t • ResourcePool.singleton (model := model access) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts ctx noQuantum t width)
      (by
        intro item present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact phaseWire_dimension ctx noQuantum t width index),
    readouts, List.length_ofFn]
  rfl

private theorem allocation_trace {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (allocationCode ctx noQuantum access).Path) :
    (allocationCode ctx noQuantum access).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model access)
    (resultContext ctx noQuantum t width) 2 t path.2

/-- Every path has exactly the independent complete source-sample event budget. -/
public theorem code_events {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code ctx noQuantum access).Path) :
    (code ctx noQuantum access).resourcePool path =
      Sampling.Native.eventBudget access := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil,
    ResourcePool.ofList_append, program_pool, measurement_pool]
  rw [preparation_pool ctx noQuantum access path.1.1]
  rfl

/-- A framed sample performs exactly one declared modular-exponentiation call. -/
public theorem code_modExpCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code ctx noQuantum access).Path) :
    ResourcePool.count (model := model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code ctx noQuantum access).resourcePool path) = 1 := by
  rw [code_events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
