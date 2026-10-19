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
public def unitaryBudget (t width : Nat) : ResourcePool (model t width) :=
  (2 * t + 3 * t.choose 2) • ResourcePool.singleton (model := model t width)
      (.gate AlgorithmGate.Coordinate.singleQubit) +
    (2 * t.choose 2 + 3 * (t / 2)) • ResourcePool.singleton (model := model t width)
      (.gate AlgorithmGate.Coordinate.cnot) +
    ResourcePool.singleton (model := model t width)
      (.oracle UnitarySource.Coordinate.ordinary)

/-- Independent full-sample budget, including storage-producing operations. -/
public def eventBudget (t width : Nat) : ResourcePool (model t width) :=
  (t + width) • ResourcePool.singleton (model := model t width)
      (.preparation (2 : ℕ+)) +
    unitaryBudget t width +
      (t • ResourcePool.singleton (model := model t width) (.measurement (2 : ℕ+)) +
        ResourcePool.singleton (model := model t width)
          (.classicalOperation (.nominalEncoding (.packFiniteBits t))))

private lemma preparation_pool (t width : Nat)
    (path : (preparationCode t width).Path) :
    ResourcePool.ofList ((preparationCode t width).eventTrace path) =
      (t + width) • ResourcePool.singleton (model := model t width)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (OrderFinding.Native.sourceModel t width) (runtimeLayout t width)
    2 (fun _ => rfl) BitWord.model .empty

private lemma program_pool (t width : Nat) :
    ResourcePool.ofList ((nativeProgram t width).eventTrace BitWord.model .empty) =
      unitaryBudget t width := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram t width) BitWord.model .empty,
    nativeProgram, Execution.unitaryOfEqualWires_cost (runtimeLayout t width)
      (preparedContext t width).quantumLayout (prepared_wires t width)
      (OrderFinding.Native.circuit t width)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((OrderFinding.Native.circuit t width).eventCost BitWord.model .empty) =
      ResourcePool.count event (unitaryBudget t width)
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

private lemma measurement_pool (t width : Nat)
    (path : (Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel t width)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts t width)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel t width)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts t width)).eventTrace path) =
      t • ResourcePool.singleton (model := model t width) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts t width)
      (by
        intro item present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact phaseWire_dimension t width index),
    readouts, List.length_ofFn]
  rfl

private lemma allocation_trace (t width : Nat)
    (path : (allocationCode t width).Path) :
    (allocationCode t width).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model t width)
    (resultContext t width) 2 t path.2

/-- Every actual full sample path has precisely the independent event budget. -/
public lemma code_events (t width : Nat) (path : (code t width).Path) :
    (code t width).resourcePool path = eventBudget t width := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil,
    ResourcePool.ofList_append, program_pool, measurement_pool]
  rw [preparation_pool t width path.1.1]
  rfl

/-- The complete stored sample makes exactly one granted modular-exponentiation call. -/
public lemma code_modExpCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code t width).resourcePool path) = 1 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Native one-qubit count includes phase preparation and inverse Fourier expansion. -/
public lemma code_singleQubitCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := model t width) (.gate .singleQubit)
      ((code t width).resourcePool path) = 2 * t + 3 * t.choose 2 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Native CNOT count includes controlled phases and each physical SWAP expansion. -/
public lemma code_cnotCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := model t width) (.gate .cnot)
      ((code t width).resourcePool path) = 2 * t.choose 2 + 3 * (t / 2) := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- The source sampler uses no native Toffoli outside the sealed query. -/
public lemma code_toffoliCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := model t width) (.gate .toffoli)
      ((code t width).resourcePool path) = 0 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Every original phase wire is measured once into an actual result cell. -/
public lemma code_measurementCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := model t width) (.measurement (2 : ℕ+))
      ((code t width).resourcePool path) = t := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- One closed bit-packing instruction writes the retained phase word. -/
public lemma code_packCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := model t width)
      (.classicalOperation (.nominalEncoding (.packFiniteBits t)))
      ((code t width).resourcePool path) = 1 := by
  rw [code_events]
  simp [eventBudget, unitaryBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.OrderFinding.Sampling.Native
