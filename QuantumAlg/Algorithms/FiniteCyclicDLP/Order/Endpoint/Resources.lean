/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Run
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Resources
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Resources
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Resources
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Resources
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete resources of the all-positive-order finite-cyclic DLP endpoint

The batch ledger, result allocation and actual all-order recovery tail belong
to one chronological execution.  Order one uses the certain two-operation
tail; every other positive order charges every checked attempt and selector.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Independent allowance of the branch selected by the known order. -/
@[expose] public def recoveryEventBudget (P : KnownOrderProblem G) :
    ResourcePool (OrderExecution.model P) :=
  if trivial : P.order = 1 then
    ResourcePool.ofList
      (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroEvents
        (OrderExecution.model P) (OrderPreparation.width P))
  else
    OrderRecovery.Native.recoveryEnvelope P (recoverySpec P trivial) (sampleCount P)

/-- Arbitrary-duration allowance of the same selected recovery branch. -/
@[expose] public def recoveryDepthLimit (P : KnownOrderProblem G)
    (duration : Resource.Event (OrderExecution.model P) → Nat) : Nat :=
  if trivial : P.order = 1 then
    duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P)
        (.wordBinary .equal (OrderPreparation.width P)))) +
    duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P)
        (.nominalEncoding (.packOption (OrderPreparation.width P)))))
  else
    OrderRecovery.Native.recoveryDepthLimit P (recoverySpec P trivial)
      (sampleCount P) duration

/-- Sampling and recovery retain separate native-operation and query coordinates. -/
@[expose] public def eventBudget (P : KnownOrderProblem G) :
    ResourcePool (OrderExecution.model P) :=
  OrderBatch.eventBudget P (sampleCount P) (OrderExecution.canonicalExpansion P) +
    recoveryEventBudget P

/-- Complete chronological dependency allowance from preparation through recovery. -/
@[expose] public def depthLimit (P : KnownOrderProblem G)
    (duration : Resource.Event (OrderExecution.model P) → Nat) : Nat :=
  OrderBatch.unitDepth P (sampleCount P) (OrderExecution.canonicalExpansion P) +
    recoveryDepthLimit P duration

/-- Independent maximum complete-cycle allowance. The full classical recovery
remains in `depthLimit` and is not assigned a quantum-cycle duration. -/
@[expose] public def completeCycleDepthLimit (P : KnownOrderProblem G) : Nat :=
  OrderBatch.unitDepth P (sampleCount P) (OrderExecution.canonicalExpansion P)

/-- Reused classical scratch is the larger of the order-one and nontrivial tails. -/
@[expose] public def recoveryScratchBudget (P : KnownOrderProblem G) : SpacePool .quantum :=
  SpacePool.max
    (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroActiveSpace
      (model := OrderExecution.model P) (OrderPreparation.width P))
    (OrderRecovery.Native.recoveryScratchSpace P)

/-- Complete resident storage includes every retained bank, cell and result,
plus the selected tail's reusable workspace. -/
@[expose] public def residentBudget (P : KnownOrderProblem G) : SpacePool .quantum :=
  recoveryScratchBudget P + (outputContext P).residentSpace

/-- Auxiliary storage is a subset account over the same complete live contexts. -/
@[expose] public def auxiliaryBudget (P : KnownOrderProblem G) : SpacePool .quantum :=
  recoveryScratchBudget P + (outputContext P).auxiliarySpace

/-- The public resource coordinates derived from the complete endpoint.

The logical-qubit coordinate covers only the two binary exponent registers.
The independently reported native group systems below prevent this projection
from inventing a binary representation of an abstract group element. -/
public structure PublicCoordinates where
  /-- Logical qubits retained by the endpoint. -/
  logicalQubits : Nat
  /-- Calls to the order-finding oracle. -/
  uxQueries : Nat
  /-- Native Toffoli gates. -/
  toffoliGates : Nat
  /-- Native CNOT gates. -/
  cnotGates : Nat
  /-- Native one-qubit gates. -/
  singleQubitGates : Nat
  /-- Whole-run dependency depth, including the classical recovery tail. -/
  wholeRunDepth : Nat
  /-- Longest complete quantum sampling cycle under unit event duration. -/
  maximumCompleteCycleDepth : Nat
  /-- Calls to the classical group-operation oracle. -/
  groupOperations : Nat
  deriving DecidableEq

/-- Closed limits for the same execution certified by `code_pool_le`,
`code_depth_le`, and the live-space theorems below. -/
@[expose] public def publicCoordinates (P : KnownOrderProblem G) : PublicCoordinates where
  logicalQubits := sampleCount P * OrderExecution.sampleWidth P
  uxQueries := sampleCount P
  toffoliGates := 0
  cnotGates := sampleCount P *
    (2 * OrderPreparation.cnotCount (OrderExecution.canonicalExpansion P) +
      2 * (2 * (OrderPreparation.width P).choose 2 +
        3 * (OrderPreparation.width P / 2)))
  singleQubitGates := sampleCount P *
    (2 * OrderPreparation.singleQubitCount (OrderExecution.canonicalExpansion P) +
      2 * (OrderPreparation.width P +
        3 * (OrderPreparation.width P).choose 2))
  wholeRunDepth := depthLimit P (fun _ => 1)
  maximumCompleteCycleDepth := completeCycleDepthLimit P
  groupOperations :=
    if P.order = 1 then 0
    else sampleCount P * (2 * OrderPreparation.width P)

/-- Each independent sample owns one native group system of the actual finite
group dimension.  These systems are deliberately separate from logical
qubits and from the public scalar coordinates. -/
@[expose] public def nativeGroupFootprint (P : KnownOrderProblem G) :
    Nat × ℕ+ :=
  (sampleCount P, OrderOracle.workspaceDimension G)

private theorem sampling_groupOperation_count_zero (P : KnownOrderProblem G) :
    ResourcePool.count (OrderRecovery.Native.groupOperationEvent P)
      (OrderBatch.eventBudget P (sampleCount P)
        (OrderExecution.canonicalExpansion P)) = 0 := by
  have measurementZero :
      ResourcePool.count (OrderRecovery.Native.groupOperationEvent P)
          (ResourcePool.singleton (model := OrderExecution.model P)
            (.measurement (2 : ℕ+))) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      simp [OrderRecovery.Native.groupOperationEvent]) 1
  unfold OrderBatch.eventBudget OrderBatch.cycleEventBudget
  rw [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  rw [ResourcePool.count_nsmul, measurementZero]
  simp [ZeroPreparation.eventCost, ZeroPreparation.eventTrace,
    ResourcePool.ofList, ResourcePool.count,
    OrderRecovery.Native.groupOperationEvent]

private theorem recoveryEventBudget_count_nonclassical
    (P : KnownOrderProblem G) (event : Resource.Event (OrderExecution.model P))
    (outsideOperation : ∀ operation, event ≠ .classicalOperation operation)
    (outsideQuery : ∀ query, event ≠ .classicalQuery query) :
    ResourcePool.count event (recoveryEventBudget P) = 0 := by
  unfold recoveryEventBudget
  split
  · simp [ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroEvents,
      ResourcePool.ofList, ResourcePool.count, outsideOperation]
  · exact OrderRecovery.Native.recoveryEnvelope_count_nonclassical
      P (recoverySpec P ‹_›) (sampleCount P) event outsideOperation outsideQuery

/-- The logical-qubit projection is exactly the exponent-register component of
the certified batch footprint. -/
public theorem publicCoordinates_logicalQubits_eq (P : KnownOrderProblem G) :
    (publicCoordinates P).logicalQubits =
      (OrderBatch.quantumFootprint P (sampleCount P)).logicalQubits := rfl

/-- The separate native-group footprint records one actual group system per
independent sample at the ambient finite-group dimension. -/
public theorem nativeGroupFootprint_eq (P : KnownOrderProblem G) :
    nativeGroupFootprint P =
      ((OrderBatch.quantumFootprint P (sampleCount P)).groupSystems,
        (OrderBatch.quantumFootprint P (sampleCount P)).groupDimension) := rfl

/-- The public query coordinate is the exact multiplicity in the certified endpoint ledger. -/
public theorem eventBudget_ux_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := OrderExecution.model P)
      (.oracle OrderOracle.Coordinate.ux) (eventBudget P) =
      (publicCoordinates P).uxQueries := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    OrderBatch.eventBudget_ux_count,
    recoveryEventBudget_count_nonclassical P (.oracle OrderOracle.Coordinate.ux)
      (by intro operation; simp) (by intro query; simp)]
  simp [publicCoordinates]

/-- The public Toffoli coordinate is the exact zero multiplicity in the
certified endpoint ledger. -/
public theorem eventBudget_toffoli_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := OrderExecution.model P)
      (.gate AlgorithmGate.Coordinate.toffoli) (eventBudget P) =
      (publicCoordinates P).toffoliGates := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    OrderBatch.eventBudget_toffoli_count,
    recoveryEventBudget_count_nonclassical P (.gate AlgorithmGate.Coordinate.toffoli)
      (by intro operation; simp) (by intro query; simp)]
  rfl

/-- The public CNOT coordinate is the exact multiplicity in the certified endpoint ledger. -/
public theorem eventBudget_cnot_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := OrderExecution.model P)
      (.gate AlgorithmGate.Coordinate.cnot) (eventBudget P) =
      (publicCoordinates P).cnotGates := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    OrderBatch.eventBudget_cnot_count,
    recoveryEventBudget_count_nonclassical P (.gate AlgorithmGate.Coordinate.cnot)
      (by intro operation; simp) (by intro query; simp)]
  simp [publicCoordinates]

/-- The public one-qubit coordinate is the exact multiplicity in the certified
endpoint ledger. -/
public theorem eventBudget_singleQubit_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := OrderExecution.model P)
      (.gate AlgorithmGate.Coordinate.singleQubit) (eventBudget P) =
      (publicCoordinates P).singleQubitGates := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    OrderBatch.eventBudget_singleQubit_count,
    recoveryEventBudget_count_nonclassical P (.gate AlgorithmGate.Coordinate.singleQubit)
      (by intro operation; simp) (by intro query; simp)]
  simp [publicCoordinates]

/-- The whole-run projection is the certified complete chronological
allowance evaluated at unit event duration. -/
public theorem publicCoordinates_wholeRunDepth_eq (P : KnownOrderProblem G) :
    (publicCoordinates P).wholeRunDepth = depthLimit P (fun _ => 1) := rfl

/-- The separately reported cycle coordinate uses the independent sampling-cycle limit. -/
public theorem publicCoordinates_maximumCompleteCycleDepth_eq (P : KnownOrderProblem G) :
    (publicCoordinates P).maximumCompleteCycleDepth = completeCycleDepthLimit P := rfl

/-- The public abstract group-operation coordinate is the exact multiplicity
reserved by the selected all-order endpoint branch. -/
public theorem eventBudget_groupOperation_count (P : KnownOrderProblem G) :
    ResourcePool.count (OrderRecovery.Native.groupOperationEvent P) (eventBudget P) =
      (publicCoordinates P).groupOperations := by
  unfold eventBudget
  rw [ResourcePool.count_add, sampling_groupOperation_count_zero]
  simp only [zero_add]
  unfold recoveryEventBudget publicCoordinates
  split
  · simp [ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroEvents,
      ResourcePool.ofList, ResourcePool.count,
      OrderRecovery.Native.groupOperationEvent]
  · rw [OrderRecovery.Native.recoveryEnvelope_groupOperation_count]

/-- The known-order branch meets its independently exposed event allowance. -/
public theorem recoveryCircuit_pool_le (P : KnownOrderProblem G) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).resourcePool path ≤ recoveryEventBudget P := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P)
          (outputRef P)).resourcePool path ≤ recoveryEventBudget P := by
      intro path
      simp only [recoveryEventBudget, dif_pos trivial]
      exact le_of_eq
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_resourcePool
          (model := OrderExecution.model P) (outputRef P) path)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).resourcePool path ≤ recoveryEventBudget P := by
      intro path
      simp only [recoveryEventBudget, dif_neg trivial]
      exact OrderRecovery.Native.recoveryInto_pool_le P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) path
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- The same branch meets its arbitrary-duration dependency allowance. -/
public theorem recoveryCircuit_depth_le (P : KnownOrderProblem G)
    (duration : Resource.Event (OrderExecution.model P) → Nat) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).depth duration path ≤ recoveryDepthLimit P duration := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P)
          (outputRef P)).depth duration path ≤ recoveryDepthLimit P duration := by
      intro path
      simp only [recoveryDepthLimit, dif_pos trivial]
      exact le_of_eq
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_durationDepth
          (model := OrderExecution.model P) (outputRef P) duration path)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).depth duration path ≤
            recoveryDepthLimit P duration := by
      intro path
      simp only [recoveryDepthLimit, dif_neg trivial]
      exact OrderRecovery.Native.recoveryInto_depth_le P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) duration path
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- Either known-order branch fits the shared endpoint resident allowance. -/
public theorem recoveryCircuit_resident_le (P : KnownOrderProblem G) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).peakResidentSpace path ≤ residentBudget P := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P)
          (outputRef P)).peakResidentSpace path ≤ residentBudget P := by
      intro path
      unfold residentBudget recoveryScratchBudget
      exact (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_resident_le
        (model := OrderExecution.model P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).peakResidentSpace path ≤ residentBudget P := by
      intro path
      unfold residentBudget recoveryScratchBudget
      exact (OrderRecovery.Native.recoveryInto_resident_le P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- Either known-order branch fits the shared endpoint auxiliary allowance. -/
public theorem recoveryCircuit_auxiliary_le (P : KnownOrderProblem G) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P)
          (outputRef P)).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
      intro path
      unfold auxiliaryBudget recoveryScratchBudget
      exact (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_auxiliary_le
        (model := OrderExecution.model P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := OrderExecution.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
      intro path
      unfold auxiliaryBudget recoveryScratchBudget
      exact (OrderRecovery.Native.recoveryInto_auxiliary_le P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- Result allocation emits no event before the selected recovery tail. -/
public theorem retainedRecovery_pool_le (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).resourcePool path ≤ recoveryEventBudget P := by
  rw [retainedRecovery_resourcePool]
  exact recoveryCircuit_pool_le P path.2

private theorem recoveryBudget_classical_event (P : KnownOrderProblem G)
    (event : Resource.Event (OrderExecution.model P))
    (present : event ∈ recoveryEventBudget P) :
    (∃ coordinate, event = .classicalOperation coordinate) ∨
      (∃ coordinate, event = .classicalQuery coordinate) := by
  cases event with
  | classicalOperation coordinate => exact Or.inl ⟨coordinate, rfl⟩
  | classicalQuery coordinate => exact Or.inr ⟨coordinate, rfl⟩
  | gate coordinate =>
      have absent := recoveryEventBudget_count_nonclassical P (.gate coordinate)
        (by intro operation; simp) (by intro query; simp)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | oracle coordinate =>
      have absent := recoveryEventBudget_count_nonclassical P (.oracle coordinate)
        (by intro operation; simp) (by intro query; simp)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | preparation dimension =>
      have absent := recoveryEventBudget_count_nonclassical P (.preparation dimension)
        (by intro operation; simp) (by intro query; simp)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | measurement dimension =>
      have absent := recoveryEventBudget_count_nonclassical P (.measurement dimension)
        (by intro operation; simp) (by intro query; simp)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)

/-- The result allocation and recovery tail contain only declared classical
operations and classical queries on every interpreter path. -/
public theorem retainedRecovery_isClassical (P : KnownOrderProblem G) :
    Circuit.IsClassical (retainedRecovery P) := by
  intro path event present
  apply recoveryBudget_classical_event P event
  apply Multiset.mem_of_le (retainedRecovery_pool_le P path)
  change event ∈ (retainedRecovery P).eventTrace path
  exact present

/-- Result allocation adds no dependency duration. -/
public theorem retainedRecovery_depth_le (P : KnownOrderProblem G)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).depth duration path ≤ recoveryDepthLimit P duration := by
  rw [retainedRecovery_depth]
  exact recoveryCircuit_depth_le P duration path.2

/-- Result retention and recovery fit the complete resident budget. -/
public theorem retainedRecovery_resident_le (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakResidentSpace path ≤ residentBudget P := by
  rw [retainedRecovery_peakResidentSpace]
  exact SpacePool.max_le
    (le_add_of_nonneg_left zero_le)
    (recoveryCircuit_resident_le P path.2)

/-- Result retention and recovery fit the complete auxiliary budget. -/
public theorem retainedRecovery_auxiliary_le (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
  rw [retainedRecovery_peakAuxiliarySpace]
  exact SpacePool.max_le
    (le_add_of_nonneg_left zero_le)
    (recoveryCircuit_auxiliary_le P path.2)

/-- Every endpoint path meets the complete sampling and recovery ledger. -/
public theorem code_pool_le (P : KnownOrderProblem G) (path : (code P).Path) :
    (code P).resourcePool path ≤ eventBudget P := by
  unfold code at path ⊢
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append, ← Circuit.resourcePool,
    OrderBatch.code_events]
  exact add_le_add le_rfl (retainedRecovery_pool_le P path.2)

/-- Every endpoint path meets the full chronological dependency allowance. -/
public theorem code_depth_le (P : KnownOrderProblem G)
    (path : (code P).Path) :
    (code P).depth (fun _ => 1) path ≤ depthLimit P (fun _ => 1) := by
  unfold code at path ⊢
  change
    (OrderBatch.code P (sampleCount P)
      (OrderExecution.canonicalExpansion P)).depth (fun _ => 1) path.1 +
      (retainedRecovery P).depth (fun _ => 1) path.2 ≤ _
  rw [OrderBatch.code_depth]
  exact Nat.add_le_add_left (retainedRecovery_depth_le P (fun _ => 1) path.2) _

/-- The public whole-run coordinate bounds the same actual sampling and
recovery execution whose maximum complete-cycle depth is reported below. -/
public theorem code_depth_le_publicCoordinates (P : KnownOrderProblem G)
    (path : (code P).Path) :
    (code P).depth (fun _ => 1) path ≤ (publicCoordinates P).wholeRunDepth := by
  rw [publicCoordinates_wholeRunDepth_eq]
  exact code_depth_le P path

/-- The full sampler and recovery tail meet the complete resident bound. -/
public theorem code_resident_le (P : KnownOrderProblem G) (path : (code P).Path) :
    (code P).peakResidentSpace path ≤ residentBudget P := by
  unfold code at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    ((OrderBatch.code_resident_le P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path.1).trans
        ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_left zero_le)))
    (retainedRecovery_resident_le P path.2)

/-- The full sampler and recovery tail meet the complete auxiliary bound. -/
public theorem code_auxiliary_le (P : KnownOrderProblem G) (path : (code P).Path) :
    (code P).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
  unfold code at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    ((OrderBatch.code_auxiliary_le P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path.1).trans
        ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_left zero_le)))
    (retainedRecovery_auxiliary_le P path.2)

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
