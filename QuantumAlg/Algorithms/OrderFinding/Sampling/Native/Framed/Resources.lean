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

private lemma preparation_pool (t width : Nat)
    (path : (preparationCode ctx noQuantum t width).Path) :
    ResourcePool.ofList ((preparationCode ctx noQuantum t width).eventTrace path) =
      (t + width) • ResourcePool.singleton (model := model t width)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (OrderFinding.Native.sourceModel t width) (Sampling.Native.runtimeLayout t width)
    2 (fun _ => rfl) BitWord.model .empty

private lemma program_pool (t width : Nat) :
    ResourcePool.ofList
      ((nativeProgram ctx noQuantum t width).eventTrace BitWord.model .empty) =
      Sampling.Native.unitaryBudget t width := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost
      (nativeProgram ctx noQuantum t width) BitWord.model .empty,
    nativeProgram, Execution.unitaryOfEqualWires_cost (Sampling.Native.runtimeLayout t width)
      (preparedContext ctx noQuantum t width).quantumLayout
      (prepared_wires ctx noQuantum t width) (OrderFinding.Native.circuit t width)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((OrderFinding.Native.circuit t width).eventCost BitWord.model .empty) =
      ResourcePool.count event (Sampling.Native.unitaryBudget t width)
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

private lemma measurement_pool (t width : Nat)
    (path : (Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel t width)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts ctx noQuantum t width)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel t width)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts ctx noQuantum t width)).eventTrace path) =
      t • ResourcePool.singleton (model := model t width) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts ctx noQuantum t width)
      (by
        intro item present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact phaseWire_dimension ctx noQuantum t width index),
    readouts, List.length_ofFn]
  rfl

private lemma allocation_trace (t width : Nat)
    (path : (allocationCode ctx noQuantum t width).Path) :
    (allocationCode ctx noQuantum t width).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model t width)
    (resultContext ctx noQuantum t width) 2 t path.2

/-- Every path has exactly the independent complete source-sample event budget. -/
public lemma code_events (t width : Nat)
    (path : (code ctx noQuantum t width).Path) :
    (code ctx noQuantum t width).resourcePool path =
      Sampling.Native.eventBudget t width := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil,
    ResourcePool.ofList_append, program_pool, measurement_pool]
  rw [preparation_pool ctx noQuantum t width path.1.1]
  rfl

/-- A framed sample performs exactly one declared modular-exponentiation call. -/
public lemma code_modExpCount (t width : Nat)
    (path : (code ctx noQuantum t width).Path) :
    ResourcePool.count (model := model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code ctx noQuantum t width).resourcePool path) = 1 := by
  rw [code_events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
