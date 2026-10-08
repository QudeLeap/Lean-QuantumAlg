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

private theorem preparation_pool {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (preparationCode E t).Path) :
    ResourcePool.ofList ((preparationCode E t).eventTrace path) =
      (t + (Elementary.helperWidth t n + n)) • ResourcePool.singleton (model := model E)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (Elementary.oracles E.source.preparation E.source.good)
    (runtimeLayout t n) 2 (fun _ => rfl) BitWord.model .empty

private theorem program_pool {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    ResourcePool.ofList ((nativeProgram E t).eventTrace BitWord.model .empty) =
      unitaryBudget E t := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram E t) BitWord.model .empty,
    nativeProgram,
    unitaryOfEqualWires_cost (runtimeLayout t n) (preparedContext t n).quantumLayout
      (prepared_canonical_wires t n) (runtimeProgram E t)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((runtimeProgram E t).eventCost BitWord.model .empty) = ResourcePool.count event _
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

private theorem measurement_pool {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles E.source.preparation E.source.good)
      (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles E.source.preparation E.source.good)
      (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).eventTrace path) =
      t • ResourcePool.singleton (model := model E) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts t n) (readouts_qubits t n),
    readouts_length]
  rfl

private theorem allocation_trace {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (allocationCode E t).Path) : (allocationCode E t).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model E) (resultContext t n) 2 t path.2

/-- Every actual path has exactly the independent complete native event pool. -/
theorem code_events {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) :
    (code E t).resourcePool path = eventBudget E t := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool E t path.1.1]
  rfl

private theorem program_depth {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    DepthExpr.depthEval (fun _ => 1) ((nativeProgram E t).eventDepth BitWord.model .empty) =
      Elementary.unitaryDepth t n := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (runtimeProgram E t).evaluatedEventDepth (fun _ => 1) = _
  rw [runtimeProgram, Elementary.castCircuit_depth,
    Elementary.program_unitDepth]

/-- Exact unit-event depth includes each preparation layer, sequential Z write and packing. -/
theorem code_depth_exact {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) :
    (code E t).depth (fun _ => 1) path =
      (if t + (Elementary.helperWidth t n + n) = 0 then 0 else 1) +
        Elementary.unitaryDepth t n + t + 1 := by
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model
        (Elementary.oracles E.source.preparation E.source.good)
        (runtimeLayout t n) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((nativeProgram E t).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model E)
        (resultContext t n) 2 t).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles E.source.preparation E.source.good)
      (operations := BitWord.model)
      (classicalOracles := .empty) (readouts t n)).depth
      (fun _ => 1) path.2.1 + 1) = _
  rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
    (Elementary.oracles E.source.preparation E.source.good) (runtimeLayout t n) 2 (fun _ => rfl)
    BitWord.model .empty, MeasurementCells.allocate_depth,
    Circuit.measurementSequence_unitDepth, readouts_length, program_depth]
  omega

/-- The independent full-cycle depth bound also covers the empty source register. -/
theorem code_depth {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) :
    (code E t).depth (fun _ => 1) path ≤ depthBudget t n := by
  rw [code_depth_exact]
  unfold depthBudget
  split <;> omega

/-- The full hybrid execution retains exactly the actual unitary's native gate count. -/
theorem code_gateCount {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code E t).resourcePool path) =
        Elementary.unitaryGateCount t n := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      Elementary.unitaryGateCount, ZeroReflection.controlledElementaryEventPool,
      ZeroReflection.controlledElementaryGateCount, ResourcePool.weightedCount_add,
      ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton] <;> ring

/-- Exact native single-qubit count of the complete amplitude-estimation run. -/
theorem aeCode_singleQubitCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.gate .singleQubit)
      ((code E t).resourcePool path) =
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
theorem aeCode_cnotCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.gate .cnot)
      ((code E t).resourcePool path) =
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
theorem aeCode_toffoliCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.gate .toffoli)
      ((code E t).resourcePool path) =
        (2 ^ t - 1) * ZeroReflection.controlledElementaryToffoliCount n := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool,
      ZeroReflection.controlledElementaryToffoliCount,
      ResourcePool.count_add, ResourcePool.count_nsmul,
      ResourcePool.count_singleton]

/-- Preparation and readout add no source queries to the actual native unitary. -/
theorem code_oracleCount {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) (coordinate : AmplitudeAmplificationSource.Coordinate) :
    ResourcePool.count (model := model E) (.oracle coordinate) ((code E t).resourcePool path) =
      (if coordinate = .preparation then 1 else 0) +
        (2 ^ t - 1) * (if coordinate = .goodReflection then 0 else 1) := by
  rw [code_events]
  cases coordinate <;> rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Ordinary preparation includes the initial query before the power ladder. -/
theorem code_preparationCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.oracle .preparation)
      ((code E t).resourcePool path) = (2 ^ t - 1) + 1 := by
  simpa [Nat.add_comm] using code_oracleCount E t path .preparation

/-- Each source step makes one ordinary inverse-preparation query. -/
theorem code_inversePreparationCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.oracle .inversePreparation)
      ((code E t).resourcePool path) = 2 ^ t - 1 := by
  simpa using code_oracleCount E t path .inversePreparation

/-- Each source step makes one explicitly granted controlled recognizer query. -/
theorem code_controlledGoodReflectionCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.oracle .controlledGoodReflection)
      ((code E t).resourcePool path) = 2 ^ t - 1 := by
  simpa using code_oracleCount E t path .controlledGoodReflection

/-- Every actual phase wire contributes one binary Z measurement. -/
theorem code_measurementCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E) (.measurement (2 : ℕ+))
      ((code E t).resourcePool path) = t := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- One packing instruction follows the actual Z-write sequence. -/
theorem code_packCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (model := model E)
      (.classicalOperation (.nominalEncoding (.packFiniteBits t)))
      ((code E t).resourcePool path) = 1 := by
  rw [code_events]
  rcases n with _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, stepBudget, readoutBudget,
      ZeroReflection.controlledElementaryEventPool, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.AmplitudeEstimation
