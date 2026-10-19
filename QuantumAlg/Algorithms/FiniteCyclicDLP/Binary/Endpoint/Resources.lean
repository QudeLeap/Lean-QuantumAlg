/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Counts
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Space
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Resources
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Resources
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Resources
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete resources of the sequential binary finite-cyclic DLP endpoint

The single-bank ledger, result allocation and actual all-order recovery tail
belong to one chronological execution. Order one uses the certain two-operation
tail; every other positive order charges every checked attempt and selector.
Each real quantum round includes physical terminal reset. The complete-run
unit-event depth allowance includes every round and the checked recovery tail
[Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Independent allowance of the branch selected by the known order. -/
@[expose] public def recoveryEventBudget (P : KnownOrderProblem G) :
    ResourcePool (Reusable.model P) :=
  if trivial : P.order = 1 then
    ResourcePool.ofList
      (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroEvents
        (Reusable.model P) (OrderPreparation.width P))
  else
    OrderRecovery.Native.recoveryEnvelope (oracles := Binary.Oracle.model P) P (recoverySpec P
      trivial) (sampleCount P)

/-- Arbitrary-duration allowance of the same selected recovery branch. -/
@[expose] public def recoveryDepthLimit (P : KnownOrderProblem G)
    (duration : Resource.Event (Reusable.model P) → Nat) : Nat :=
  if trivial : P.order = 1 then
    duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := Reusable.model P)
        (.wordBinary .equal (OrderPreparation.width P)))) +
    duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := Reusable.model P)
        (.nominalEncoding (.packOption (OrderPreparation.width P)))))
  else
    OrderRecovery.Native.recoveryDepthLimit (oracles := Binary.Oracle.model P) P (recoverySpec
      P trivial)
      (sampleCount P) duration

/-- Sampling and recovery retain separate native-operation and query coordinates. -/
@[expose] public def eventBudget (P : KnownOrderProblem G) :
    ResourcePool (Reusable.model P) :=
  Reusable.eventBudget P (sampleCount P) (OrderExecution.canonicalExpansion P) +
    recoveryEventBudget P

/-- Complete chronological dependency allowance from preparation through recovery. -/
@[expose] public def depthLimit (P : KnownOrderProblem G)
    (duration : Resource.Event (Reusable.model P) → Nat) : Nat :=
  Reusable.unitDepth P (sampleCount P) (OrderExecution.canonicalExpansion P) +
    recoveryDepthLimit P duration

/-- Reused classical scratch is the larger of the order-one and nontrivial tails. -/
@[expose] public def recoveryScratchBudget (P : KnownOrderProblem G) : SpacePool .quantum :=
  SpacePool.max
    (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroActiveSpace
      (model := Reusable.model P) (OrderPreparation.width P))
    (OrderRecovery.Native.recoveryScratchSpace P)

/-- Complete resident storage includes the one bank, every retained cell and the result,
plus the selected tail's reusable workspace. -/
@[expose] public def residentBudget (P : KnownOrderProblem G) : SpacePool .quantum :=
  recoveryScratchBudget P + (outputContext P).residentSpace

/-- Auxiliary storage is a subset account over the same complete live contexts. -/
@[expose] public def auxiliaryBudget (P : KnownOrderProblem G) : SpacePool .quantum :=
  recoveryScratchBudget P + (outputContext P).auxiliarySpace

/-- The public resource coordinates derived from the complete endpoint.

The logical-qubit coordinate is the one physical binary bank shared by every
sample. The final reset and the ambient-group recovery tail belong to the same
complete execution. -/
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
  /-- Calls to the classical group-operation oracle. -/
  groupOperations : Nat
  deriving DecidableEq

/-- Closed limits for the same execution certified by `binaryEndpoint_code_pool_le`,
`binaryEndpoint_code_depth_le`, and the live-space theorems below. -/
@[expose] public def publicCoordinates (P : KnownOrderProblem G) : PublicCoordinates where
  logicalQubits := Reusable.bankWidth P
  uxQueries := sampleCount P
  toffoliGates := 0
  cnotGates := sampleCount P *
    (2 * OrderPreparation.cnotCount (OrderExecution.canonicalExpansion P) +
      2 * (2 * (OrderPreparation.width P).choose 2 +
        3 * (OrderPreparation.width P / 2)))
  singleQubitGates := sampleCount P *
    (2 * OrderPreparation.singleQubitCount (OrderExecution.canonicalExpansion P) +
      2 * (OrderPreparation.width P +
        3 * (OrderPreparation.width P).choose 2) + Reusable.bankWidth P)
  wholeRunDepth := depthLimit P (fun _ => 1)
  groupOperations :=
    if P.order = 1 then 0
    else sampleCount P * (2 * OrderPreparation.width P)

private lemma sampling_groupOperation_count_zero (P : KnownOrderProblem G) :
    ResourcePool.count (OrderRecovery.Native.groupOperationEvent (oracles :=
      Binary.Oracle.model P) P)
      (Reusable.eventBudget P (sampleCount P)
        (OrderExecution.canonicalExpansion P)) = 0 := by
  unfold Reusable.eventBudget Reusable.roundEventBudget
  rw [ResourcePool.count_add, ResourcePool.count_scale, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  simp [ZeroPreparation.eventCost, ZeroPreparation.eventTrace,
    ResourcePool.ofList, ResourcePool.count, ResourcePool.singleton,
    ZReset.Bank.envelope, ZReset.eventEnvelope,
    OrderRecovery.Native.groupOperationEvent]

private lemma recoveryEventBudget_count_nonclassical
    (P : KnownOrderProblem G) (event : Resource.Event (Reusable.model P))
    (outsideOperation : ∀ operation, event ≠ .classicalOperation operation)
    (outsideQuery : ∀ query, event ≠ .classicalQuery query) :
    ResourcePool.count event (recoveryEventBudget P) = 0 := by
  unfold recoveryEventBudget
  split
  · simp [ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroEvents,
      ResourcePool.ofList, ResourcePool.count, outsideOperation]
  · exact OrderRecovery.Native.recoveryEnvelope_count_nonclassical (oracles :=
    Binary.Oracle.model P)
      P (recoverySpec P ‹_›) (sampleCount P) event outsideOperation outsideQuery

/-- The public query coordinate is the exact multiplicity in the certified endpoint ledger. -/
public lemma binaryEndpoint_eventBudget_ux_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := Reusable.model P)
      (.oracle OrderOracle.Coordinate.ux) (eventBudget P) =
      (publicCoordinates P).uxQueries := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    Reusable.eventBudget_query_count,
    recoveryEventBudget_count_nonclassical P (.oracle OrderOracle.Coordinate.ux)
      (by intro operation; simp) (by intro query; simp)]
  simp [publicCoordinates]

/-- The public CNOT coordinate is the exact multiplicity in the certified endpoint ledger. -/
public lemma binaryEndpoint_eventBudget_cnot_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := Reusable.model P)
      (.gate AlgorithmGate.Coordinate.cnot) (eventBudget P) =
      (publicCoordinates P).cnotGates := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    Reusable.reusableDLP_eventBudget_cnot_count,
    recoveryEventBudget_count_nonclassical P (.gate AlgorithmGate.Coordinate.cnot)
      (by intro operation; simp) (by intro query; simp)]
  simp [publicCoordinates]

/-- The public one-qubit coordinate is the exact multiplicity in the certified
endpoint ledger. -/
public lemma binaryEndpoint_eventBudget_singleQubit_count (P : KnownOrderProblem G) :
    ResourcePool.count (model := Reusable.model P)
      (.gate AlgorithmGate.Coordinate.singleQubit) (eventBudget P) =
      (publicCoordinates P).singleQubitGates := by
  unfold eventBudget
  rw [ResourcePool.count_add,
    Reusable.reusableDLP_eventBudget_singleQubit_count,
    recoveryEventBudget_count_nonclassical P (.gate AlgorithmGate.Coordinate.singleQubit)
      (by intro operation; simp) (by intro query; simp)]
  simp [publicCoordinates]

/-- The whole-run projection is the certified complete chronological
allowance evaluated at unit event duration. -/
public lemma binaryEndpoint_publicCoordinates_wholeRunDepth_eq (P : KnownOrderProblem G) :
    (publicCoordinates P).wholeRunDepth = depthLimit P (fun _ => 1) := rfl

/-- The public abstract group-operation coordinate is the exact multiplicity
reserved by the selected all-order endpoint branch. -/
public lemma binaryEndpoint_eventBudget_groupOperation_count (P : KnownOrderProblem G) :
    ResourcePool.count (OrderRecovery.Native.groupOperationEvent (oracles :=
      Binary.Oracle.model P) P) (eventBudget P) =
      (publicCoordinates P).groupOperations := by
  unfold eventBudget
  rw [ResourcePool.count_add, sampling_groupOperation_count_zero]
  simp only [zero_add]
  unfold recoveryEventBudget publicCoordinates
  split
  · simp [ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroEvents,
      ResourcePool.ofList, ResourcePool.count,
      OrderRecovery.Native.groupOperationEvent]
  · rw [OrderRecovery.Native.recoveryEnvelope_groupOperation_count (oracles :=
    Binary.Oracle.model P)]

/-- The known-order branch meets its independently exposed event allowance. -/
public lemma binaryEndpoint_recoveryCircuit_pool_le (P : KnownOrderProblem G) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).resourcePool path ≤ recoveryEventBudget P := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P)
          (outputRef P)).resourcePool path ≤ recoveryEventBudget P := by
      intro path
      simp only [recoveryEventBudget, dif_pos trivial]
      exact le_of_eq
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_resourcePool
          (model := Reusable.model P) (outputRef P) path)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).resourcePool path ≤ recoveryEventBudget P := by
      intro path
      simp only [recoveryEventBudget, dif_neg trivial]
      exact OrderRecovery.Native.recoveryInto_pool_le (oracles := Binary.Oracle.model P) P
        (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) path
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- The same branch meets its arbitrary-duration dependency allowance. -/
public lemma binaryEndpoint_recoveryCircuit_depth_le (P : KnownOrderProblem G)
    (duration : Resource.Event (Reusable.model P) → Nat) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).depth duration path ≤ recoveryDepthLimit P duration := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P)
          (outputRef P)).depth duration path ≤ recoveryDepthLimit P duration := by
      intro path
      simp only [recoveryDepthLimit, dif_pos trivial]
      exact le_of_eq
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_durationDepth
          (model := Reusable.model P) (outputRef P) duration path)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).depth duration path ≤
            recoveryDepthLimit P duration := by
      intro path
      simp only [recoveryDepthLimit, dif_neg trivial]
      exact OrderRecovery.Native.recoveryInto_depth_le (oracles := Binary.Oracle.model P) P
        (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) duration path
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- Either known-order branch fits the shared endpoint resident allowance. -/
public lemma binaryEndpoint_recoveryCircuit_resident_le (P : KnownOrderProblem G) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).peakResidentSpace path ≤ residentBudget P := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P)
          (outputRef P)).peakResidentSpace path ≤ residentBudget P := by
      intro path
      unfold residentBudget recoveryScratchBudget
      exact (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_resident_le
        (model := Reusable.model P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).peakResidentSpace path ≤ residentBudget P := by
      intro path
      unfold residentBudget recoveryScratchBudget
      exact (OrderRecovery.Native.recoveryInto_resident_le (oracles := Binary.Oracle.model P) P
        (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- Either known-order branch fits the shared endpoint auxiliary allowance. -/
public lemma binaryEndpoint_recoveryCircuit_auxiliary_le (P : KnownOrderProblem G) :
    ∀ path : (recoveryCircuit P).Path,
      (recoveryCircuit P).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
  by_cases trivial : P.order = 1
  · have branch : ∀ path :
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P)).Path,
        (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P)
          (outputRef P)).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
      intro path
      unfold auxiliaryBudget recoveryScratchBudget
      exact (ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_auxiliary_le
        (model := Reusable.model P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto
          (model := Reusable.model P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch
  · have branch : ∀ path :
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).Path,
        (OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P)).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
      intro path
      unfold auxiliaryBudget recoveryScratchBudget
      exact (OrderRecovery.Native.recoveryInto_auxiliary_le (oracles := Binary.Oracle.model P)
        P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P) path).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
    have circuitEq : recoveryCircuit P =
        OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
          trivial) (sampleCount P)
          (retainedSample P) (outputRef P) := by
      simp [recoveryCircuit, trivial]
    exact circuitEq.symm ▸ branch

/-- Result allocation emits no event before the selected recovery tail. -/
public lemma binaryEndpoint_retainedRecovery_pool_le (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).resourcePool path ≤ recoveryEventBudget P := by
  rw [binaryEndpoint_retainedRecovery_resourcePool]
  exact binaryEndpoint_recoveryCircuit_pool_le P path.2

private lemma recoveryBudget_classical_event (P : KnownOrderProblem G)
    (event : Resource.Event (Reusable.model P))
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
public lemma binaryEndpoint_retainedRecovery_isClassical (P : KnownOrderProblem G) :
    Circuit.IsClassical (retainedRecovery P) := by
  intro path event present
  apply recoveryBudget_classical_event P event
  apply Multiset.mem_of_le (binaryEndpoint_retainedRecovery_pool_le P path)
  change event ∈ (retainedRecovery P).eventTrace path
  exact present

/-- Result allocation adds no dependency duration. -/
public lemma binaryEndpoint_retainedRecovery_depth_le (P : KnownOrderProblem G)
    (duration : Resource.Event (Reusable.model P) → Nat)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).depth duration path ≤ recoveryDepthLimit P duration := by
  rw [binaryEndpoint_retainedRecovery_depth]
  exact binaryEndpoint_recoveryCircuit_depth_le P duration path.2

/-- Result retention and recovery fit the complete resident budget. -/
public lemma binaryEndpoint_retainedRecovery_resident_le (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakResidentSpace path ≤ residentBudget P := by
  rw [binaryEndpoint_retainedRecovery_peakResidentSpace]
  exact SpacePool.max_le
    (le_add_of_nonneg_left zero_le)
    (binaryEndpoint_recoveryCircuit_resident_le P path.2)

/-- Result retention and recovery fit the complete auxiliary budget. -/
public lemma binaryEndpoint_retainedRecovery_auxiliary_le (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
  rw [binaryEndpoint_retainedRecovery_peakAuxiliarySpace]
  exact SpacePool.max_le
    (le_add_of_nonneg_left zero_le)
    (binaryEndpoint_recoveryCircuit_auxiliary_le P path.2)

/-- Every endpoint path meets the complete sampling and recovery ledger. -/
public lemma binaryEndpoint_code_pool_le (P : KnownOrderProblem G) (path : (code P).Path) :
    (code P).resourcePool path ≤ eventBudget P := by
  unfold code at path ⊢
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append, ← Circuit.resourcePool]
  exact add_le_add
    (Reusable.reusableDLP_code_events_le P (sampleCount P) (OrderExecution.canonicalExpansion
      P) path.1)
    (binaryEndpoint_retainedRecovery_pool_le P path.2)

/-- Every endpoint path meets the full chronological dependency allowance. -/
public lemma binaryEndpoint_code_depth_le (P : KnownOrderProblem G)
    (path : (code P).Path) :
    (code P).depth (fun _ => 1) path ≤ depthLimit P (fun _ => 1) := by
  unfold code at path ⊢
  change
    (Reusable.code P (sampleCount P)
      (OrderExecution.canonicalExpansion P)).depth (fun _ => 1) path.1 +
      (retainedRecovery P).depth (fun _ => 1) path.2 ≤ _
  exact Nat.add_le_add
    (Reusable.reusableDLP_code_depth_le P (sampleCount P) (OrderExecution.canonicalExpansion P)
      path.1)
    (binaryEndpoint_retainedRecovery_depth_le P (fun _ => 1) path.2)

/-- The public whole-run coordinate bounds the same actual sampling and
recovery execution, including every chronological section. -/
public lemma binaryEndpoint_code_depth_le_publicCoordinates (P : KnownOrderProblem G)
    (path : (code P).Path) :
    (code P).depth (fun _ => 1) path ≤ (publicCoordinates P).wholeRunDepth := by
  rw [binaryEndpoint_publicCoordinates_wholeRunDepth_eq]
  exact binaryEndpoint_code_depth_le P path

/-- The full sampler and recovery tail meet the complete resident bound. -/
public lemma binaryEndpoint_code_resident_le (P : KnownOrderProblem G) (path : (code P).Path) :
    (code P).peakResidentSpace path ≤ residentBudget P := by
  unfold code at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    ((Reusable.reusableDLP_code_resident_le P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path.1).trans
        ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_left zero_le)))
    (binaryEndpoint_retainedRecovery_resident_le P path.2)

/-- The full sampler and recovery tail meet the complete auxiliary bound. -/
public lemma binaryEndpoint_code_auxiliary_le (P : KnownOrderProblem G) (path : (code P).Path) :
    (code P).peakAuxiliarySpace path ≤ auxiliaryBudget P := by
  unfold code at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    ((Reusable.reusableDLP_code_auxiliary_le P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path.1).trans
        ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_left zero_le)))
    (binaryEndpoint_retainedRecovery_auxiliary_le P path.2)

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
