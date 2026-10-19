/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Resources of the actual single-bank finite-cyclic sampler

Every real round includes the native word, the retained exponent measurements,
and one complete terminal reset. Only the initial prefix prepares a bank.
The budgets below are independent of the particular measurement path
[Sho95, source.tex:1713-1984] [dW19, qcnotes.tex:5405-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- One unchanged native word, all exponent readouts, and one full-bank reset. -/
public def roundEventBudget (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) : ResourcePool (model P) :=
  (Binary.Circuit.circuit P expansion).eventCost BitWord.model
      (ClassicalFiniteGroupOracle.model G) +
    (sampleWidth P • ResourcePool.singleton (model := model P) (.measurement (2 : ℕ+)) +
      ZReset.Bank.envelope (services := ClassicalFiniteGroupOracle.model G)
        (oracles := Binary.Oracle.model P) (bankWidth P) BitWord.model)

/-- One physical allocation followed by the actual number of complete rounds. -/
public def eventBudget (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) : ResourcePool (model P) :=
  ZeroPreparation.eventCost AlgorithmGate.model (Binary.Oracle.model P)
      (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G) +
    ResourcePool.scale count (roundEventBudget P expansion)

/-- A single unitary word followed by exponent measurement and full physical reset. -/
public def roundUnitDepth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) : Nat :=
  OrderPreparation.unitDepth expansion + 1 +
    (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
      (if OrderPreparation.width P / 2 = 0 then 0 else 3)) + sampleWidth P + 2 * bankWidth P

private lemma readout_pool (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (path : (QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
      (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (readouts P slot)).Path) :
    (QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      (readouts P slot)).resourcePool path =
      sampleWidth P • ResourcePool.singleton (model := model P) (.measurement (2 : ℕ+)) := by
  rw [QuantumAlg.Circuit.measurementSequence_qubit_resourcePool (readouts P slot)
    (fun item _ => qubits P count item.wire)]
  simp only [readouts, List.length_ofFn]
  rfl

/-- The allowance covers every path of this same native, measured and reset round. -/
public lemma round_events_le (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) (path : (round P slot expansion).Path) :
    (round P slot expansion).resourcePool path ≤ roundEventBudget P expansion := by
  unfold round at path ⊢
  rcases path with ⟨nativePath, readoutPath, resetPath⟩
  have resetBound := ZReset.Bank.zResetBank_resourcePool_le
    (services := ClassicalFiniteGroupOracle.model G) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (qubits P count) (scratch P count) resetPath
  rw [context_systemCount] at resetBound
  have program : ResourcePool.ofList
      ((nativeProgram P count expansion).eventTrace BitWord.model
        (ClassicalFiniteGroupOracle.model G)) =
      (Binary.Circuit.circuit P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G) := by
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost
      (nativeProgram P count expansion) BitWord.model (ClassicalFiniteGroupOracle.model G),
      nativeProgram, Execution.unitaryOfEqualWires_cost]
  change ResourcePool.ofList (_ ++ (_ ++ _)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  change ResourcePool.ofList
      ((nativeProgram P count expansion).eventTrace BitWord.model
        (ClassicalFiniteGroupOracle.model G)) +
    ((QuantumAlg.Circuit.measurementSequence (allowAllocation := true)
      (readouts P slot)).resourcePool readoutPath +
      (reset P count).resourcePool resetPath) ≤ _
  rw [program, readout_pool]
  exact add_le_add le_rfl (add_le_add le_rfl resetBound)

/-- Repetition adds the events of all actual rounds without adding another bank. -/
public lemma rounds_events_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (rounds P count expansion).Path) :
    (rounds P count expansion).resourcePool path ≤
      ResourcePool.scale count (roundEventBudget P expansion) :=
  QuantumAlg.Circuit.forRange_pool_le count (fun slot => round P slot expansion)
    (roundEventBudget P expansion) (fun slot => round_events_le P slot expansion) path

private lemma allocation_trace (P : KnownOrderProblem G) (count : Nat)
    (path : (allocationCode P count).Path) :
    (allocationCode P count).eventTrace path = [] := by
  change (MeasurementCells.allocate (model := model P) (bankContext P) 2
      (count * sampleWidth P)).eventTrace path.1 ++ [] = []
  rw [MeasurementCells.allocate_eventTrace, List.nil_append]

/-- The prefix pays only the one real binary-bank preparation. -/
public lemma initialCode_events (P : KnownOrderProblem G) (count : Nat)
    (path : (initialCode P count).Path) :
    (initialCode P count).resourcePool path =
      ZeroPreparation.eventCost AlgorithmGate.model (Binary.Oracle.model P)
        (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G) := by
  change ResourcePool.ofList (_ ++ _) = _
  rw [ResourcePool.ofList_append, allocation_trace, ResourcePool.ofList_nil, add_zero]
  rfl

/-- All physical preparation, every round, and the final reset share this one ledger. -/
public lemma reusableDLP_code_events_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).resourcePool path ≤ eventBudget P count expansion := by
  change ResourcePool.ofList ((_ ++ _) ++ _) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, allocation_trace,
    ResourcePool.ofList_nil, add_zero]
  exact add_le_add le_rfl (rounds_events_le P count expansion path.2)

private lemma program_depth (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram P count expansion).eventDepth BitWord.model
        (ClassicalFiniteGroupOracle.model G)) =
      OrderPreparation.unitDepth expansion + 1 +
        (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
          (if OrderPreparation.width P / 2 = 0 then 0 else 3)) := by
  rw [nativeProgram, Execution.unitaryOfEqualWires_depth,
    UnitaryCircuit.unitaryCircuit_unit_depth_classical_context,
    Binary.Circuit.binaryCircuit_circuit_unit_depth, OrderPreparation.Native.circuit_unit_depth]

/-- Quantum events in one actual round include its terminal physical reset. -/
public lemma round_depth_le (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) (path : (round P slot expansion).Path) :
    (round P slot expansion).depth (fun _ => 1) path ≤ roundUnitDepth P expansion := by
  unfold round at path ⊢
  rcases path with ⟨nativePath, readoutPath, resetPath⟩
  have resetBound := ZReset.Bank.zResetBank_unitDepth_le
    (services := ClassicalFiniteGroupOracle.model G) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (qubits P count) (scratch P count) resetPath
  rw [context_systemCount] at resetBound
  change (reset P count).depth (fun _ => 1) resetPath ≤ 2 * bankWidth P at resetBound
  rw [QuantumAlg.Circuit.depth_seq, QuantumAlg.Circuit.depth_seq,
    QuantumAlg.Circuit.measurementSequence_unitDepth]
  change DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram P count expansion).eventDepth BitWord.model
        (ClassicalFiniteGroupOracle.model G)) +
      ((readouts P slot).length + (reset P count).depth (fun _ => 1) resetPath) ≤ _
  rw [program_depth]
  simp only [readouts, List.length_ofFn]
  unfold roundUnitDepth
  omega

/-- Whole-run quantum chronology keeps the prefix and every sequential round. -/
public def unitDepth (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) : Nat :=
  1 + count * roundUnitDepth P expansion

/-- Actual classical cell allocation contributes no dependency duration. -/
public lemma allocationCode_depth (P : KnownOrderProblem G) (count : Nat)
    (duration : Resource.Event (model P) → Nat)
    (path : (allocationCode P count).Path) :
    (allocationCode P count).depth duration path = 0 := by
  change (MeasurementCells.allocate (model := model P) (bankContext P) 2
    (count * sampleWidth P)).depth duration path.1 + 0 = 0
  rw [MeasurementCells.allocate_depth, zero_add]

/-- The only physical preparation prefix uses at most one parallel layer. -/
public lemma initialCode_depth_le (P : KnownOrderProblem G) (count : Nat)
    (path : (initialCode P count).Path) :
    (initialCode P count).depth (fun _ => 1) path ≤ 1 := by
  change (preparationCode P).depth (fun _ => 1) path.1 +
    (allocationCode P count).depth (fun _ => 1) path.2 ≤ 1
  rw [allocationCode_depth, add_zero]
  change DepthExpr.depthEval (fun _ => 1)
    (ZeroPreparation.eventDepth AlgorithmGate.model (Binary.Oracle.model P)
      (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G)) ≤ 1
  rw [ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model (Binary.Oracle.model P)
    (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G)]
  split <;> omega

/-- The full sampler keeps chronological depth separate from maximum per-round depth. -/
public lemma reusableDLP_code_depth_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).depth (fun _ => 1) path ≤ unitDepth P count expansion := by
  have allRounds := QuantumAlg.Circuit.forRange_depth_le count
    (fun slot => round P slot expansion) (roundUnitDepth P expansion)
    (fun slot => round_depth_le P slot expansion) path.2
  change (initialCode P count).depth (fun _ => 1) path.1 +
    (rounds P count expansion).depth (fun _ => 1) path.2 ≤ _
  exact Nat.add_le_add (initialCode_depth_le P count path.1) allRounds

omit [Fintype G] in
/-- Classical retention changes no bank dimension or physical identity. -/
public lemma reusableDLP_context_resident (P : KnownOrderProblem G) (count : Nat) :
    (context P count).residentSpace =
      SpacePool.ofShape (.finite 2) +
        ((count * sampleWidth P) • SpacePool.ofShape (.finite 2) +
          SpacePool.ofQuantumLayout (Binary.Oracle.layout P)) := by
  rw [context, RuntimeCtx.residentSpace_addRetained, sampleContext,
    MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout]
  rfl

end

end QuantumAlg.FiniteCyclicDLP.Reusable
