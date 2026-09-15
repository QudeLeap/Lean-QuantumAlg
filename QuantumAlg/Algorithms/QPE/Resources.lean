/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Depth.EventCount
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Primitives.WalshHadamard
import Mathlib.Data.List.OfFn

/-!
# Exact complete phase-estimation events and depth

Every actual path charges one all-zero preparation, the source-correct
unitary, each retained-cell Z write, and the final packing opcode. The
complete trace is compared with explicit independent event and depth formulas.
The granted controlled-U calls remain a distinct native source coordinate.

-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

private theorem preparation_value (t : Nat) (index : Fin t) :
    ((inputPreparation t).value index).val = 0 := by
  change (finTwoEquiv.symm ((0 : Fin (2 ^ t)).val.testBit index.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

theorem inputPreparation_event (t : Nat) :
    (inputPreparation t).event = basisPreparationEvent t := by
  have dimensions : (phaseRuntimeLayout t).dimensions.map PNat.val = List.replicate t 2 := by
    change (List.ofFn (fun _ : Fin t => (2 : ℕ+))).map PNat.val = _
    rw [List.map_ofFn]
    exact List.ofFn_const t 2
  have values : List.ofFn (fun index => ((inputPreparation t).value index).val) =
      List.replicate t 0 := by
    simp only [preparation_value, List.ofFn_const]
  change Resource.Event.preparation
    { family := "builtin", name := "computational-basis",
      parameters := t ::
        ((phaseRuntimeLayout t).dimensions.map PNat.val ++
          List.ofFn (fun index => ((inputPreparation t).value index).val)) } = _
  rw [dimensions, values]
  rfl

private theorem program_pool {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    ResourcePool.ofList (nativeProgram P t).eventTrace =
      ResourcePool.singleton (.gate (.builtin "hadamard")) t +
        (2 ^ t - 1) • ResourcePool.singleton (qpeControlledSourceUnitaryEvent n) +
        (t • ResourcePool.singleton (.gate (.builtin "hadamard")) +
          t.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
          (t / 2) • ResourcePool.singleton (.gate (.builtin "swap"))) := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
    UnitaryCircuit.reindex_eventCost, qpeCircuit_eventCost,
    qpeReadoutCircuit_eventCost, QFTCircuit_eventCost_eq]
  rfl

private theorem measurement_pool (t n : Nat)
    (path : (Circuit.measurementSequence (readouts t n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (readouts t n)).eventTrace path) =
      t • ResourcePool.singleton (Circuit.zEvent 2) := by
  change (Circuit.measurementSequence (readouts t n)).resourcePool path = _
  rw [Circuit.measurementSequence_qubit_resourcePool (readouts t n) (readouts_qubits t n),
    readouts_length]

private theorem packing_trace (t n : Nat) :
    (packing t n).eventTrace =
      [.classicalOperation (.nominalEncoding (.packFiniteBits t))] :=
  ClassicalOp.eventTrace_packFiniteBits t _ _ _

private theorem allocation_trace (t n : Nat) (path : (allocationCode t n).Path) :
    (allocationCode t n).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (resultContext t n) 2 t path.2

/-- Every actual path has exactly the independent complete native event pool. -/
theorem code_events {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (code P t).Path) :
    (code P t).resourcePool path = eventBudget t n := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    preparationCode, allocation_trace, Circuit.eventTrace,
    List.append_nil, ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero, inputPreparation_event, program_pool,
    measurement_pool, packing_trace]
  rfl

private theorem program_depth_le {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    (nativeProgram P t).evaluatedEventDepth (fun _ => 1) ≤
      t + (2 ^ t - 1) + (t + t.choose 2 + t / 2) := by
  have pool := program_pool P t
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost] at pool
  calc
    _ ≤ DepthExpr.costEval (fun _ => 1) (nativeProgram P t).eventDepth :=
      DepthExpr.depthEval_le_costEval (fun _ => 1) (nativeProgram P t).eventDepth
    _ = (nativeProgram P t).eventCost.card :=
      (DepthExpr.unitCost_eq_eventPool_card (nativeProgram P t).eventDepth).trans
        (congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost _))
    _ = _ := by rw [pool]; simp [ResourcePool.singleton]

/-- The critical path is bounded by the independent total of actual event occurrences. -/
theorem code_depth {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (path : (code P t).Path) :
    (code P t).depth (fun _ => 1) path ≤ depthBudget t := by
  change (1 + ((nativeProgram P t).evaluatedEventDepth (fun _ => 1) +
    (0 + (MeasurementCells.allocate (resultContext t n) 2 t).depth
      (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (readouts t n)).depth (fun _ => 1) path.2.1 + 1) ≤ _
  rw [MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth, readouts_length]
  have bounded := program_depth_le P t
  unfold depthBudget
  omega

/-- Preparation, Z measurements and packing add no source-unitary calls. -/
theorem code_quantumSubroutineCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (code P t).Path) (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) ((code P t).resourcePool path) =
      ResourcePool.count (.quantumSubroutine label) (qpeCircuit t P.unitary).eventCost := by
  rw [code_events, qpeCircuit_eventCost, qpeReadoutCircuit_eventCost, QFTCircuit_eventCost_eq]
  simp [eventBudget, basisPreparationEvent, WalshHadamard.hadamardEvent]

/-- Every path contains exactly the original controlled-U query multiplicity. -/
theorem code_controlledUnitaryCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (code P t).Path) :
    ResourcePool.count (qpeControlledSourceUnitaryEvent n)
      ((code P t).resourcePool path) = 2 ^ t - 1 :=
  (code_quantumSubroutineCount P t path
    ((EndpointDeclarations.qpeSourceUnitarySubroutineLabel n).quantum.controlForDimension 2)).trans
      (qpeCircuit_controlledMultiplicity t P.unitary)

end

end QuantumAlg.QuantumPhaseEstimation
