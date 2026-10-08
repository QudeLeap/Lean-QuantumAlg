/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Program
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Trace.Preparation

/-!
# Resources of independent known-order samples

Every repetition has its own exponent registers and native-dimensional group
system. All banks are prepared in one parallel layer and their source words
use the certified disjoint parallel construction. Retained measurements remain
in explicit chronological order. The group systems remain separate from
logical qubit counts and from any bit encoding.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Exact native ledger of one bank after its initial preparation. -/
public def cycleEventBudget (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) : ResourcePool (OrderExecution.model P) :=
  (OrderCircuit.circuit P expansion).eventCost BitWord.model
      (ClassicalFiniteGroupOracle.model G) +
    OrderExecution.sampleWidth P •
      ResourcePool.singleton (model := OrderExecution.model P) (.measurement (2 : ℕ+))

/-- One parallel fresh preparation followed by every chronological sample. -/
public def eventBudget (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) : ResourcePool (OrderExecution.model P) :=
  ZeroPreparation.eventCost AlgorithmGate.model (OrderOracle.model P)
      (layout P count) BitWord.model (ClassicalFiniteGroupOracle.model G) +
    count • cycleEventBudget P expansion

/-- Exact unit-duration dependency depth of one source word. -/
public def programUnitDepth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) : Nat :=
  OrderPreparation.unitDepth expansion + 1 +
    (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
      3 * (OrderPreparation.width P / 2))

/-- Complete critical-path depth, including parallel preparation and source
words followed by the explicit terminal readout sequence. -/
public def unitDepth (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) : Nat :=
  (if count * bankSize P = 0 then 0 else 1) +
    (if count = 0 then 0 else programUnitDepth P expansion) +
    count * OrderExecution.sampleWidth P

/-- Live quantum systems are reported without assigning a group-element bit width. -/
public structure QuantumFootprint where
  /-- Qubits in all exponent-register banks. -/
  logicalQubits : Nat
  /-- Native-dimensional group systems, one per independent bank. -/
  groupSystems : Nat
  /-- Dimension of every group system. -/
  groupDimension : ℕ+
  deriving DecidableEq

/-- Exact logical and native-dimensional system counts of the complete bank family. -/
@[expose] public def quantumFootprint (P : KnownOrderProblem G)
    (count : Nat) : QuantumFootprint where
  logicalQubits := count * OrderExecution.sampleWidth P
  groupSystems := count
  groupDimension := OrderOracle.workspaceDimension G

private theorem preparation_gate_count_zero (P : KnownOrderProblem G) (count : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := OrderExecution.model P) (.gate coordinate)
      (ZeroPreparation.eventCost AlgorithmGate.model (OrderOracle.model P)
        (layout P count) BitWord.model (ClassicalFiniteGroupOracle.model G)) = 0 := by
  simp [ZeroPreparation.eventCost, ZeroPreparation.eventTrace,
    ResourcePool.count, ResourcePool.ofList]

private theorem preparation_oracle_count_zero (P : KnownOrderProblem G) (count : Nat) :
    ResourcePool.count (model := OrderExecution.model P) (.oracle .ux)
      (ZeroPreparation.eventCost AlgorithmGate.model (OrderOracle.model P)
        (layout P count) BitWord.model (ClassicalFiniteGroupOracle.model G)) = 0 := by
  simp [ZeroPreparation.eventCost, ZeroPreparation.eventTrace,
    ResourcePool.count, ResourcePool.ofList]

private theorem circuit_singleQubit_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .singleQubit)
      ((OrderCircuit.circuit P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G)) =
      2 * OrderPreparation.singleQubitCount expansion +
        2 * (OrderPreparation.width P + 3 * (OrderPreparation.width P).choose 2) := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact OrderCircuit.circuit_singleQubit_count P expansion

private theorem circuit_cnot_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .cnot)
      ((OrderCircuit.circuit P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G)) =
      2 * OrderPreparation.cnotCount expansion +
        2 * (2 * (OrderPreparation.width P).choose 2 +
          3 * (OrderPreparation.width P / 2)) := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact OrderCircuit.circuit_cnot_count P expansion

private theorem circuit_toffoli_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .toffoli)
      ((OrderCircuit.circuit P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G)) = 0 := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact OrderCircuit.circuit_toffoli_count P expansion

private theorem circuit_ux_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.oracle .ux)
      ((OrderCircuit.circuit P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G)) = 1 := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact OrderCircuit.circuit_ux_count P expansion

/-- Exact single-qubit count of all independent native sample banks. -/
public theorem eventBudget_singleQubit_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .singleQubit)
      (eventBudget P count expansion) =
      count *
        (2 * OrderPreparation.singleQubitCount expansion +
          2 * (OrderPreparation.width P + 3 * (OrderPreparation.width P).choose 2)) := by
  unfold eventBudget cycleEventBudget
  rw [ResourcePool.count_add, preparation_gate_count_zero,
    ResourcePool.count_nsmul, ResourcePool.count_add,
    circuit_singleQubit_count]
  simp

/-- Exact CNOT count of all independent native sample banks. -/
public theorem eventBudget_cnot_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .cnot)
      (eventBudget P count expansion) =
      count *
        (2 * OrderPreparation.cnotCount expansion +
          2 * (2 * (OrderPreparation.width P).choose 2 +
            3 * (OrderPreparation.width P / 2))) := by
  unfold eventBudget cycleEventBudget
  rw [ResourcePool.count_add, preparation_gate_count_zero,
    ResourcePool.count_nsmul, ResourcePool.count_add,
    circuit_cnot_count]
  simp

/-- The sampler uses no Toffoli gate: range preparation and inverse QFT are
already literal one-qubit/CNOT words. -/
public theorem eventBudget_toffoli_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .toffoli)
      (eventBudget P count expansion) = 0 := by
  unfold eventBudget cycleEventBudget
  rw [ResourcePool.count_add, preparation_gate_count_zero,
    ResourcePool.count_nsmul, ResourcePool.count_add,
    circuit_toffoli_count]
  simp

/-- Every independent bank invokes the sole granted quantum oracle once. -/
public theorem eventBudget_ux_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := OrderExecution.model P) (.oracle .ux)
      (eventBudget P count expansion) = count := by
  unfold eventBudget cycleEventBudget
  rw [ResourcePool.count_add, preparation_oracle_count_zero,
    ResourcePool.count_nsmul, ResourcePool.count_add,
    circuit_ux_count]
  simp

private theorem readouts_length (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) : (readouts P slot).length = OrderExecution.sampleWidth P := by
  simp [readouts]

private theorem readouts_qubits (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (item : ZReadout (post P count))
    (present : item ∈ readouts P slot) :
    ((post P count).quantumLayout.wire item.wire).dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact exponent_dimension P slot index

private theorem allReadouts_length (P : KnownOrderProblem G) (count : Nat) :
    (allReadouts P count).length = count * OrderExecution.sampleWidth P := by
  rw [allReadouts, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  simp [readouts_length]

private theorem allReadouts_qubits (P : KnownOrderProblem G) (count : Nat)
    (item : ZReadout (post P count)) (present : item ∈ allReadouts P count) :
    ((post P count).quantumLayout.wire item.wire).dimension = 2 := by
  rw [allReadouts, List.mem_flatten] at present
  obtain ⟨bank, bankPresent, itemPresent⟩ := present
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp bankPresent
  exact readouts_qubits P slot item itemPresent

private theorem measurement_pool (P : KnownOrderProblem G) (count : Nat)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderOracle.model P) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (allReadouts P count)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderOracle.model P) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (allReadouts P count)).eventTrace path) =
        (count * OrderExecution.sampleWidth P) •
          ResourcePool.singleton (model := OrderExecution.model P)
            (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool
      (allReadouts P count) (allReadouts_qubits P count),
    allReadouts_length]
  rfl

private theorem programs_pool (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (programs P count expansion).Path) :
    (programs P count expansion).resourcePool path =
      count • (OrderCircuit.circuit P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G) := by
  change ResourcePool.ofList
    ((nativeFamilyProgram P count expansion).eventTrace BitWord.model
      (ClassicalFiniteGroupOracle.model G)) = _
  calc
    _ = (nativeFamilyProgram P count expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G) :=
      UnitaryCircuit.ofList_eventTrace_eq_eventCost
        (nativeFamilyProgram P count expansion) BitWord.model
          (ClassicalFiniteGroupOracle.model G)
    _ = _ := by
      rw [nativeFamilyProgram, Execution.unitaryOfEqualWires_cost, familyProgram_eventCost]

private theorem preparation_pool (P : KnownOrderProblem G) (count : Nat)
    (path : (preparationCode P count).Path) :
    (preparationCode P count).resourcePool path =
      ZeroPreparation.eventCost AlgorithmGate.model (OrderOracle.model P)
        (layout P count) BitWord.model (ClassicalFiniteGroupOracle.model G) := by
  rfl

private theorem allocation_trace (P : KnownOrderProblem G) (count : Nat)
    (path : (allocationCode P count).Path) :
    (allocationCode P count).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := OrderExecution.model P)
    (bankContext P count) 2 (count * OrderExecution.sampleWidth P) path

/-- Every actual batch path has exactly the exposed independent ledger. -/
public theorem code_events (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).resourcePool path = eventBudget P count expansion := by
  unfold code beforeMeasurement at path ⊢
  unfold eventBudget
  rcases path with
    ⟨⟨preparationPath, ⟨allocationPath, programPath⟩⟩, measurementPath⟩
  unfold readoutCode at measurementPath
  change
    (preparationCode P count).resourcePool preparationPath +
        ((allocationCode P count).resourcePool allocationPath +
          (programs P count expansion).resourcePool programPath) +
      (readoutCode P count).resourcePool measurementPath = _
  rw [preparation_pool, programs_pool]
  change _ + (ResourcePool.ofList
      ((allocationCode P count).eventTrace allocationPath) + _) +
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderOracle.model P) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (allReadouts P count)).eventTrace measurementPath) = _
  rw [measurement_pool P count measurementPath]
  rw [allocation_trace, ResourcePool.ofList_nil, zero_add]
  unfold cycleEventBudget
  rw [nsmul_add, mul_nsmul]
  simp only [add_assoc]
  rw [smul_comm (OrderExecution.sampleWidth P) count]

private theorem programs_depth (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (programs P count expansion).Path) :
    (programs P count expansion).depth (fun _ => 1) path =
      if count = 0 then 0 else programUnitDepth P expansion := by
  change DepthExpr.depthEval (fun _ => 1)
    ((nativeFamilyProgram P count expansion).eventDepth BitWord.model
      (ClassicalFiniteGroupOracle.model G)) = _
  rw [nativeFamilyProgram, Execution.unitaryOfEqualWires_depth,
    familyProgram_unitDepth]
  congr 1
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context,
    OrderCircuit.circuit_unit_depth,
    OrderPreparation.Native.circuit_unit_depth]
  rfl

private theorem measurement_depth (P : KnownOrderProblem G) (count : Nat)
    (path : (readoutCode P count).Path) :
    (readoutCode P count).depth (fun _ => 1) path =
      count * OrderExecution.sampleWidth P := by
  unfold readoutCode at path ⊢
  rw [Circuit.measurementSequence_unitDepth, allReadouts_length]

private theorem preparation_depth (P : KnownOrderProblem G) (count : Nat)
    (path : (preparationCode P count).Path) :
    (preparationCode P count).depth (fun _ => 1) path =
      if count * bankSize P = 0 then 0 else 1 := by
  unfold preparationCode at path ⊢
  change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (OrderOracle.model P)
        (layout P count) BitWord.model (ClassicalFiniteGroupOracle.model G)) = _
  exact ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model
    (OrderOracle.model P) (layout P count) BitWord.model
    (ClassicalFiniteGroupOracle.model G)

private theorem allocation_depth (P : KnownOrderProblem G) (count : Nat)
    (path : (allocationCode P count).Path) :
    (allocationCode P count).depth (fun _ => 1) path = 0 := by
  unfold allocationCode
  exact MeasurementCells.allocate_depth (model := OrderExecution.model P)
    (bankContext P count) 2 (count * OrderExecution.sampleWidth P) (fun _ => 1) path

/-- Every batch path has the same complete critical-path unit depth. -/
public theorem code_depth (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).depth (fun _ => 1) path = unitDepth P count expansion := by
  unfold code beforeMeasurement at path ⊢
  unfold unitDepth
  rcases path with ⟨⟨preparationPath, allocationPath, programPath⟩, measurementPath⟩
  rw [Circuit.depth_seq, Circuit.depth_seq, Circuit.depth_seq,
    preparation_depth, allocation_depth, programs_depth, measurement_depth, zero_add]

/-- The terminal context contains every bank and exactly all retained sample cells. -/
public theorem post_residentSpace (P : KnownOrderProblem G) (count : Nat) :
    (post P count).residentSpace =
      (count * OrderExecution.sampleWidth P) • SpacePool.ofShape (.finite 2) +
        SpacePool.ofQuantumLayout (layout P count) := by
  rw [post, MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, OrderExecution.pre_residentSpace, add_zero]

/-- The terminal context counts the same owned systems and retained cells as auxiliary. -/
public theorem post_auxiliarySpace (P : KnownOrderProblem G) (count : Nat) :
    (post P count).auxiliarySpace =
      (count * OrderExecution.sampleWidth P) • SpacePool.ofShape (.finite 2) +
        SpacePool.ofQuantumLayout (layout P count) := by
  rw [post, MeasurementCells.context_auxiliarySpace, bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout]
  rfl

private theorem measurementSequence_resident
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (readouts : List (ZReadout ctx))
    (path : (Circuit.measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).Path) :
    (Circuit.measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).peakResidentSpace
        path = ctx.residentSpace := by
  induction readouts with
  | nil => exact Circuit.peakResidentSpace_id path
  | cons head tail induction =>
      change SpacePool.max ctx.residentSpace
        ((Circuit.measurementSequence (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := classicalOracles)
          tail).peakResidentSpace path.2) = ctx.residentSpace
      rw [induction, SpacePool.max_self]

private theorem measurementSequence_auxiliary
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (readouts : List (ZReadout ctx))
    (path : (Circuit.measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).Path) :
    (Circuit.measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).peakAuxiliarySpace
        path = ctx.auxiliarySpace := by
  induction readouts with
  | nil => exact Circuit.peakAuxiliarySpace_id path
  | cons head tail induction =>
      change SpacePool.max ctx.auxiliarySpace
        ((Circuit.measurementSequence (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := classicalOracles)
          tail).peakAuxiliarySpace path.2) = ctx.auxiliarySpace
      rw [induction, SpacePool.max_self]

private theorem readout_resident (P : KnownOrderProblem G) (count : Nat)
    (path : (readoutCode P count).Path) :
    (readoutCode P count).peakResidentSpace path = (post P count).residentSpace := by
  exact measurementSequence_resident (allReadouts P count) path

private theorem readout_auxiliary (P : KnownOrderProblem G) (count : Nat)
    (path : (readoutCode P count).Path) :
    (readoutCode P count).peakAuxiliarySpace path = (post P count).auxiliarySpace := by
  exact measurementSequence_auxiliary (allReadouts P count) path

/-- Every sampler path peaks at the complete native bank and retained-cell context. -/
public theorem code_resident_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).peakResidentSpace path ≤ (post P count).residentSpace := by
  unfold code beforeMeasurement at path ⊢
  rw [Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_seq]
  refine SpacePool.max_le (SpacePool.max_le ?_ (SpacePool.max_le ?_ ?_)) ?_
  · unfold preparationCode bankContext at path ⊢
    rw [Circuit.prepare_peakResidentSpace]
    exact MeasurementCells.context_residentSpace_mono
      (bankContext P count) 2 (Nat.zero_le (count * OrderExecution.sampleWidth P))
  · exact MeasurementCells.allocate_peakResidentSpace
      (model := OrderExecution.model P) (bankContext P count) 2
        (count * OrderExecution.sampleWidth P) path.1.2.1
  · exact le_of_eq (Circuit.peakResidentSpace_unitary _ path.1.2.2)
  · exact le_of_eq (readout_resident P count path.2)

/-- The same actual path bounds the complete auxiliary-role peak. -/
public theorem code_auxiliary_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    (code P count expansion).peakAuxiliarySpace path ≤ (post P count).auxiliarySpace := by
  unfold code beforeMeasurement at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_seq]
  refine SpacePool.max_le (SpacePool.max_le ?_ (SpacePool.max_le ?_ ?_)) ?_
  · unfold preparationCode bankContext at path ⊢
    rw [Circuit.prepare_peakAuxiliarySpace]
    exact MeasurementCells.context_auxiliarySpace_mono
      (bankContext P count) 2 (Nat.zero_le (count * OrderExecution.sampleWidth P))
  · exact MeasurementCells.allocate_peakAuxiliarySpace
      (model := OrderExecution.model P) (bankContext P count) 2
        (count * OrderExecution.sampleWidth P) path.1.2.1
  · exact le_of_eq (Circuit.peakAuxiliarySpace_unitary _ path.1.2.2)
  · exact le_of_eq (readout_auxiliary P count path.2)

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch
