/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Primitives.WalshHadamard
import Mathlib.Data.List.OfFn

/-!
# Complete native amplitude-estimation events and depth

The source query and actual elementary reflection sequences provide the
unitary events and parallel-layer depth. The complete execution additionally
charges preparation of every phase, source and selected work system, the t actual
source Z writes and one packing opcode. Every equality observes the same
interpreter trace and an independently defined parameter-only budget.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

private lemma preparation_pool (n : Nat) (t : Nat)
    (path : (preparationCode n t).Path) :
    ResourcePool.ofList ((preparationCode n t).eventTrace path) =
      (t + (Elementary.helperWidth t n + n)) • ResourcePool.singleton (model := model n)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (Elementary.oracles n)
    (runtimeLayout t n) 2 (fun _ => rfl) BitWord.model .empty

private lemma program_pool (n : Nat) (t : Nat) :
    ResourcePool.ofList ((nativeProgram n t).eventTrace BitWord.model .empty) =
      unitaryBudget n t := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram n t) BitWord.model .empty,
    nativeProgram,
    unitaryOfEqualWires_cost (runtimeLayout t n) (preparedContext t n).quantumLayout
      (prepared_canonical_wires t n) (runtimeProgram n t)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((runtimeProgram n t).eventCost BitWord.model .empty) = ResourcePool.count event _
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      change AlgorithmGate.Coordinate at coordinate
      cases coordinate <;>
        rcases n with _ | _ | _ | n <;>
        simp [runtimeProgram, Elementary.castCircuit_cost, Elementary.program_eventCost,
          Elementary.unitaryEventPool, Elementary.stepEventPool, Elementary.readoutEventPool,
          unitaryBudget, stepBudget, readoutBudget,
          ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | oracle coordinate =>
      change AmplitudeAmplificationSource.Coordinate at coordinate
      cases coordinate <;>
        rcases n with _ | _ | _ | n <;>
        simp [runtimeProgram, Elementary.castCircuit_cost, Elementary.program_eventCost,
          Elementary.unitaryEventPool, Elementary.stepEventPool, Elementary.readoutEventPool,
          unitaryBudget, stepBudget, readoutBudget,
          ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | _ =>
      rcases n with _ | _ | _ | n <;>
        simp [unitaryBudget, stepBudget, readoutBudget,
          ZeroReflection.controlledElementaryEventPool,
          ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

private lemma measurement_pool (n : Nat) (t : Nat)
    (path : (Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles n)
      (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles n)
      (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).eventTrace path) =
      t • ResourcePool.singleton (model := model n) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts t n) (readouts_qubits t n),
    readouts_length]
  rfl

private lemma allocation_trace (n : Nat) (t : Nat)
    (path : (allocationCode n t).Path) : (allocationCode n t).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model n) (resultContext t n) 2 t path.2

/-- Every actual path has exactly the independent complete native event pool. -/
lemma code_events (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    (code n t).resourcePool path = eventBudget n t := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool n t path.1.1]
  rfl

private lemma program_depth (n : Nat) (t : Nat) :
    DepthExpr.depthEval (fun _ => 1) ((nativeProgram n t).eventDepth BitWord.model .empty) =
      Elementary.unitaryCriticalPath t n := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (runtimeProgram n t).evaluatedEventDepth (fun _ => 1) = _
  rw [runtimeProgram, Elementary.castCircuit_depth,
    Elementary.program_unitDepth]

/-- Exact unit-event depth includes each preparation layer, sequential Z write and packing. -/
lemma code_depth_exact (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    (code n t).depth (fun _ => 1) path =
      (if t + (Elementary.helperWidth t n + n) = 0 then 0 else 1) +
        Elementary.unitaryCriticalPath t n + t + 1 := by
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model
        (Elementary.oracles n)
        (runtimeLayout t n) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((nativeProgram n t).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model n)
        (resultContext t n) 2 t).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles n)
      (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).depth
      (fun _ => 1) path.2.1 + 1) = _
  rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
    (Elementary.oracles n) (runtimeLayout t n) 2 (fun _ => rfl)
    BitWord.model .empty, MeasurementCells.allocate_depth,
    Circuit.measurementSequence_unitDepth, readouts_length, program_depth]
  omega

/-- The independent complete execution bound also covers the empty source register. -/
lemma code_depth (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    (code n t).depth (fun _ => 1) path ≤ depthBudget t n := by
  rw [code_depth_exact]
  have bounded := Elementary.unitaryCriticalPath_le_unitaryDepth t n
  unfold depthBudget
  split <;> omega

/-- The full hybrid execution retains exactly the actual unitary's native gate count. -/
lemma code_gateCount (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code n t).resourcePool path) =
        Elementary.unitaryGateCount t n := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      Elementary.unitaryGateCount, ZeroReflection.controlledElementaryEventPool,
      ZeroReflection.controlledElementaryGateCount, ResourcePool.weightedCount_add,
      ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton] <;> ring

/-- Exact native single-qubit count of the complete amplitude-estimation run. -/
lemma aeCode_singleQubitCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.gate .singleQubit)
      ((code n t).resourcePool path) =
        2 * t + (2 ^ t - 1) * ZeroReflection.controlledElementarySingleQubitCount n +
          3 * t.choose 2 := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool,
      ZeroReflection.controlledElementarySingleQubitCount,
      ResourcePool.count_add, ResourcePool.count_nsmul,
      ResourcePool.count_singleton] <;> ring

/-- Exact native CNOT count, including the inverse-Fourier readout. -/
lemma aeCode_cnotCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.gate .cnot)
      ((code n t).resourcePool path) =
        (2 ^ t - 1) * ZeroReflection.controlledElementaryCNOTCount n +
          2 * t.choose 2 + 3 * (t / 2) := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool,
      ZeroReflection.controlledElementaryCNOTCount,
      ResourcePool.count_add, ResourcePool.count_nsmul,
      ResourcePool.count_singleton, Nat.add_assoc]

/-- Exact native Toffoli count of the repeated controlled zero reflection. -/
lemma aeCode_toffoliCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.gate .toffoli)
      ((code n t).resourcePool path) =
        (2 ^ t - 1) * ZeroReflection.controlledElementaryToffoliCount n := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool,
      ZeroReflection.controlledElementaryToffoliCount,
      ResourcePool.count_add, ResourcePool.count_nsmul,
      ResourcePool.count_singleton]

/-- Preparation and readout add no source queries to the actual native unitary. -/
lemma code_oracleCount (n : Nat) (t : Nat)
    (path : (code n t).Path) (coordinate : AmplitudeAmplificationSource.Coordinate) :
    ResourcePool.count (model := model n) (.oracle coordinate) ((code n t).resourcePool path) =
      (if coordinate = .preparation then 1 else 0) +
        (2 ^ t - 1) * (if coordinate = .goodReflection then 0 else 1) := by
  rw [code_events]
  cases coordinate <;> rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Ordinary preparation includes the initial query before the power ladder. -/
lemma code_preparationCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.oracle .preparation)
      ((code n t).resourcePool path) = (2 ^ t - 1) + 1 := by
  simpa [Nat.add_comm] using code_oracleCount n t path .preparation

/-- Each source step makes one ordinary inverse-preparation query. -/
lemma code_inversePreparationCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.oracle .inversePreparation)
      ((code n t).resourcePool path) = 2 ^ t - 1 := by
  simpa using code_oracleCount n t path .inversePreparation

/-- Each source step makes one explicitly granted controlled recognizer query. -/
lemma code_controlledGoodReflectionCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.oracle .controlledGoodReflection)
      ((code n t).resourcePool path) = 2 ^ t - 1 := by
  simpa using code_oracleCount n t path .controlledGoodReflection

/-- Every actual phase wire contributes one binary Z measurement. -/
lemma code_measurementCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n) (.measurement (2 : ℕ+))
      ((code n t).resourcePool path) = t := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- One packing instruction follows the actual Z-write sequence. -/
lemma code_packCount (n : Nat)
    (t : Nat) (path : (code n t).Path) :
    ResourcePool.count (model := model n)
      (.classicalOperation (.nominalEncoding (.packFiniteBits t)))
      ((code n t).resourcePool path) = 1 := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.AmplitudeEstimation
