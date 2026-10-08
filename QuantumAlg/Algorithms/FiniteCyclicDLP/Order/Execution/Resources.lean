/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Exact resources of one finite-cyclic DLP sampling cycle

The ledger contains the mixed-dimensional zero preparation, the generated
native unitary, and every sequential exponent-qubit measurement.  Logical
exponent qubits and the one native group system are reported separately, so
the abstract group order is never reinterpreted as an encoding width.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExecution

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Exact literal event ledger of one complete cycle. -/
public def eventBudget (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    ResourcePool (model P) :=
  ZeroPreparation.eventCost AlgorithmGate.model (OrderOracle.model P)
      (OrderOracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G) +
    (nativeProgram P expansion).eventCost BitWord.model
      (ClassicalFiniteGroupOracle.model G) +
    sampleWidth P • ResourcePool.singleton (model := model P) (.measurement (2 : ℕ+))

/-- Complete unit depth includes preparation, one unitary stage, and all ordered measurements. -/
public def unitDepth (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) : Nat :=
  1 + OrderPreparation.unitDepth expansion + 1 +
    (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
      3 * (OrderPreparation.width P / 2)) + sampleWidth P

/-- Exact event ledger of the canonical all-positive-order cycle. -/
public def canonicalEventBudget (P : KnownOrderProblem G) : ResourcePool (model P) :=
  eventBudget P (canonicalExpansion P)

/-- Exact depth of the canonical all-positive-order cycle. -/
public def canonicalUnitDepth (P : KnownOrderProblem G) : Nat :=
  unitDepth P (canonicalExpansion P)

/-- The public quantum footprint keeps logical qubits separate from the abstract group system. -/
public structure QuantumFootprint where
  /-- Qubit systems in the two exponent registers. -/
  logicalQubits : Nat
  /-- Native-dimensional systems used for group elements. -/
  groupSystems : Nat
  /-- Dimension of each group system for this endpoint. -/
  groupDimension : ℕ+
  deriving DecidableEq

/-- Two exponent registers and one actual native-dimensional group system remain live. -/
public def quantumFootprint (P : KnownOrderProblem G) : QuantumFootprint where
  logicalQubits := sampleWidth P
  groupSystems := 1
  groupDimension := OrderOracle.workspaceDimension G

private theorem readouts_length (P : KnownOrderProblem G) :
    (readouts P).length = sampleWidth P := by
  simp [readouts]

private theorem readouts_qubits (P : KnownOrderProblem G)
    (item : ZReadout (post P)) (present : item ∈ readouts P) :
    ((post P).quantumLayout.wire item.wire).dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact exponent_dimension P index

private theorem allocation_trace (P : KnownOrderProblem G)
    (path : (allocationCode P).Path) : (allocationCode P).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model P) (bankContext P) 2
    (sampleWidth P) path

private theorem preparation_pool (P : KnownOrderProblem G)
    (path : (preparationCode P).Path) :
    ResourcePool.ofList ((preparationCode P).eventTrace path) =
      ZeroPreparation.eventCost AlgorithmGate.model (OrderOracle.model P)
        (OrderOracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G) := by
  rfl

private theorem program_pool (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.ofList
      ((nativeProgram P expansion).eventTrace BitWord.model
        (ClassicalFiniteGroupOracle.model G)) =
      (nativeProgram P expansion).eventCost BitWord.model
        (ClassicalFiniteGroupOracle.model G) := by
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (nativeProgram P expansion) BitWord.model (ClassicalFiniteGroupOracle.model G)

private theorem measurement_pool (P : KnownOrderProblem G)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderOracle.model P) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G) (readouts P)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderOracle.model P) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (readouts P)).eventTrace path) =
        sampleWidth P •
          ResourcePool.singleton (model := model P) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts P) (readouts_qubits P),
    readouts_length]
  rfl

/-- Every interpreter path has exactly the independently exposed complete ledger. -/
public theorem code_events (P : KnownOrderProblem G) (expansion : OrderExpansion P.order)
    (path : (code P expansion).Path) :
    (code P expansion).resourcePool path = eventBudget P expansion := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace,
    ResourcePool.ofList_append, ResourcePool.ofList_nil, zero_add, program_pool,
    measurement_pool, preparation_pool]
  unfold eventBudget
  abel

/-- Every path of the canonical cycle has its exact canonical ledger. -/
public theorem canonicalCode_events (P : KnownOrderProblem G)
    (path : (canonicalCode P).Path) :
    (canonicalCode P).resourcePool path = canonicalEventBudget P := by
  exact code_events P (canonicalExpansion P) path

private theorem program_depth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram P expansion).eventDepth BitWord.model
        (ClassicalFiniteGroupOracle.model G)) =
      OrderPreparation.unitDepth expansion + 1 +
        (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
          3 * (OrderPreparation.width P / 2)) := by
  rw [nativeProgram_eventDepth,
    UnitaryCircuit.unitaryCircuit_unit_depth_classical_context,
    OrderCircuit.circuit_unit_depth,
    OrderPreparation.Native.circuit_unit_depth]

private theorem preparation_code_depth (P : KnownOrderProblem G)
    (path : (preparationCode P).Path) :
    (preparationCode P).depth (fun _ => 1) path = 1 := by
  unfold preparationCode
  change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (OrderOracle.model P)
        (OrderOracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G)) = 1
  rw [ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model
    (OrderOracle.model P) (OrderOracle.layout P) BitWord.model
    (ClassicalFiniteGroupOracle.model G)]
  simp

private theorem allocation_code_depth (P : KnownOrderProblem G)
    (path : (allocationCode P).Path) :
    (allocationCode P).depth (fun _ => 1) path = 0 := by
  unfold allocationCode
  exact MeasurementCells.allocate_depth (model := model P)
    (bankContext P) 2 (sampleWidth P) (fun _ => 1) path

private theorem unitary_code_depth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (path : (Circuit.unitary (nativeProgram P expansion) :
      Circuit (model P) (post P) (post P)).Path) :
    (Circuit.unitary (nativeProgram P expansion) :
      Circuit (model P) (post P) (post P)).depth (fun _ => 1) path =
        OrderPreparation.unitDepth expansion + 1 +
          (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
            3 * (OrderPreparation.width P / 2)) := by
  change DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram P expansion).eventDepth BitWord.model
        (ClassicalFiniteGroupOracle.model G)) = _
  exact program_depth P expansion

/-- Exact maximal circuit depth of one full preparation-to-measurement cycle. -/
public theorem code_depth (P : KnownOrderProblem G) (expansion : OrderExpansion P.order)
    (path : (code P expansion).Path) :
    (code P expansion).depth (fun _ => 1) path = unitDepth P expansion := by
  unfold code beforeMeasurement readoutCode at path ⊢
  rcases path with
    ⟨⟨preparationPath, ⟨allocationPath, programPath⟩⟩, measurementPath⟩
  rw [Circuit.depth_seq, Circuit.depth_seq, Circuit.depth_seq,
    preparation_code_depth, allocation_code_depth, unitary_code_depth,
    Circuit.measurementSequence_unitDepth, readouts_length]
  unfold unitDepth
  omega

/-- Every path of the canonical cycle has its exact canonical depth. -/
public theorem canonicalCode_depth (P : KnownOrderProblem G)
    (path : (canonicalCode P).Path) :
    (canonicalCode P).depth (fun _ => 1) path = canonicalUnitDepth P := by
  exact code_depth P (canonicalExpansion P) path

/-- The final live context contains the bank and exactly all raw measurement cells. -/
public theorem post_residentSpace (P : KnownOrderProblem G) :
    (post P).residentSpace =
      sampleWidth P • SpacePool.ofShape (.finite 2) +
        SpacePool.ofQuantumLayout (OrderOracle.layout P) := by
  rw [post, MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, pre_residentSpace, add_zero]

end

end QuantumAlg.FiniteCyclicDLP.OrderExecution
