/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Resources.Modulus
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Complete all-positive-order finite-cyclic DLP run

The canonical retry count supplies fresh native-dimensional samples.  One
retained optional word is then written by either the certain order-one routine
or the representation-independent recovery and group-verification tail.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

open Execution

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Number of actual samples used by the two-thirds amplification. -/
public abbrev sampleCount (P : KnownOrderProblem G) : Nat :=
  FiniteCyclicDLP.Canonical.retryCount P

/-- Complete post-sampling context before the result is allocated. -/
public abbrev sampledContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  OrderBatch.post P (sampleCount P)

/-- Fresh key of the single retained optional result. -/
@[expose] public def outputKey (P : KnownOrderProblem G) : StorageKey :=
  (sampledContext P).canonicalFreshKey

public theorem outputKey_fresh (P : KnownOrderProblem G) :
    outputKey P ∉ (sampledContext P).keys :=
  RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampledContext P)

/-- Samples, native group systems and the final optional word all remain live. -/
@[expose] public def outputContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  (sampledContext P).addRetained (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)

/-- Writable destination of the one actual endpoint result. -/
@[expose] public def outputRef (P : KnownOrderProblem G) :
    CWriteRef (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) :=
  CWriteRef.retainedHead (sampledContext P) (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)

/-- One retained sample transported through result allocation. -/
@[expose] public def retainedSample (P : KnownOrderProblem G) (slot : Fin (sampleCount P)) :
    CInputRef (outputContext P)
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)) :=
  (OrderBatch.sampleInput P slot).underRetained (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)

/-- The nontrivial modular recovery specification follows solely from the known order. -/
@[expose] public def recoverySpec (P : KnownOrderProblem G) (nontrivial : P.order ≠ 1) :
    ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P) :=
  Canonical.resourceModulusSpec P (by
    have positive := P.order_pos
    omega)

/-- Order one returns zero certainly; every other positive order executes the
complete raw recovery, abstract group power and target comparison. -/
@[expose] public def recoveryCircuit (P : KnownOrderProblem G) :
    Circuit (OrderExecution.model P) (outputContext P) (outputContext P) :=
  if trivial : P.order = 1 then
    ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto (outputRef P)
  else
    OrderRecovery.Native.recoveryInto P (recoverySpec P trivial) (sampleCount P)
      (retainedSample P) (outputRef P)

/-- Order one selects the literal zero-writing recovery branch. -/
public theorem recoveryCircuit_order_one (P : KnownOrderProblem G)
    (trivial : P.order = 1) :
    recoveryCircuit P =
      ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto (outputRef P) := by
  exact dif_pos trivial

/-- Every nontrivial positive order selects checked native recovery. -/
public theorem recoveryCircuit_nontrivial (P : KnownOrderProblem G)
    (nontrivial : P.order ≠ 1) :
    recoveryCircuit P =
      OrderRecovery.Native.recoveryInto P (recoverySpec P nontrivial) (sampleCount P)
        (retainedSample P) (outputRef P) := by
  exact dif_neg nontrivial

/-- Allocate the result cell behind the abstract endpoint context boundary. -/
public def outputAllocation (P : KnownOrderProblem G) :
    Circuit (OrderExecution.model P) (sampledContext P) (outputContext P) :=
  .retain (model := OrderExecution.model P) (sampledContext P) (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)

/-- The allocation instruction has its unique execution path. -/
public def outputAllocationPath (P : KnownOrderProblem G) :
    (outputAllocation P).Path := ()

/-- Classical record produced by the result-cell allocation. -/
public def retainedEntry (P : KnownOrderProblem G) {History : Type}
    (entry : Store (sampledContext P) ×
      ((OrderExecution.model P).HiddenState × History)) :
    Store (outputContext P) ×
      ((OrderExecution.model P).HiddenState × (History × (outputAllocation P).Path)) :=
    (entry.1.pushRetained (outputKey P)
      (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P),
        (entry.2.1, (entry.2.2, outputAllocationPath P)))

/-- Actual result allocation preserves the hidden service state and appends one path unit. -/
public def retainedState (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((OrderExecution.model P).HiddenState × History)) :
    State (outputContext P) Reference
      ((OrderExecution.model P).HiddenState × (History × (outputAllocation P).Path)) :=
  state.mapClassical (retainedEntry P)

/-- Allocating a result cell preserves normalization. -/
public theorem retainedState_normalized (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((OrderExecution.model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    (retainedState P state).IsNormalized := by
  exact state.mapClassical_normalized normalized (retainedEntry P)

/-- Result allocation pushes forward only the finite classical record law. -/
public theorem retainedState_toPMF (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((OrderExecution.model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    (retainedState P state).toPMF (retainedState_normalized P state normalized) =
      (state.toPMF normalized).map (retainedEntry P) := by
  exact ExecutionState.toPMF_mapClassical state normalized (retainedEntry P)

/-- Result allocation preserves every sample read under its retained reference. -/
public theorem retainedEntry_read_sample (P : KnownOrderProblem G) {History : Type}
    (entry : Store (sampledContext P) ×
      ((OrderExecution.model P).HiddenState × History))
    (index : Fin (sampleCount P)) :
    (retainedEntry P entry).1.read (retainedSample P index) =
      entry.1.read (OrderBatch.sampleInput P index) := by
  exact Store.read_pushRetained_underRetained entry.1 (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)
      (OrderBatch.sampleInput P index)

/-- The literal retained-cell instruction executes as `retainedState`. -/
public theorem outputRetain_execute (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((OrderExecution.model P).HiddenState × History)) :
    (outputAllocation P).execute Reference state = retainedState P state := by
  unfold outputAllocation retainedState retainedEntry outputAllocationPath
  refine (Circuit.execute_retain (model := OrderExecution.model P)
      (ctx := sampledContext P) (Reference := Reference) state (outputKey P)
        (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)).trans ?_
  exact ExecutionState.executionState_mapClassical_congr state rfl

/-- Result allocation emits no native event. -/
public theorem outputAllocation_eventTrace (P : KnownOrderProblem G)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).eventTrace path = [] := by
  unfold outputAllocation
  rfl

/-- Result allocation adds no dependency duration. -/
public theorem outputAllocation_depth (P : KnownOrderProblem G)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).depth duration path = 0 := by
  unfold outputAllocation
  rfl

/-- Allocation visits exactly the original and retained resident contexts. -/
public theorem outputAllocation_peakResidentSpace (P : KnownOrderProblem G)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).peakResidentSpace path =
      (outputContext P).residentSpace := by
  unfold outputAllocation
  exact Circuit.peakResidentSpace_retain _ _ _ path

/-- Allocation visits exactly the original and retained auxiliary contexts. -/
public theorem outputAllocation_peakAuxiliarySpace (P : KnownOrderProblem G)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).peakAuxiliarySpace path =
      (outputContext P).auxiliarySpace := by
  unfold outputAllocation
  exact Circuit.peakAuxiliarySpace_retain _ _ _ path

/-- Allocate the result only after every quantum sample has completed. -/
public abbrev retainedRecovery (P : KnownOrderProblem G) :
    Circuit (OrderExecution.model P) (sampledContext P) (outputContext P) :=
  .seq (outputAllocation P) (recoveryCircuit P)

/-- Result retention is the literal allocation followed by the selected recovery branch. -/
public theorem retainedRecovery_sequence (P : KnownOrderProblem G) :
    retainedRecovery P =
      .seq (outputAllocation P) (recoveryCircuit P) := rfl

/-- Allocating the result emits no resource event before recovery. -/
public theorem retainedRecovery_resourcePool (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).resourcePool path =
      (recoveryCircuit P).resourcePool path.2 := by
  change ResourcePool.ofList
    ((outputAllocation P).eventTrace path.1 ++
      (recoveryCircuit P).eventTrace path.2) = _
  rw [outputAllocation_eventTrace, List.nil_append]
  rfl

/-- Allocating the result adds no dependency duration before recovery. -/
public theorem retainedRecovery_depth (P : KnownOrderProblem G)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).depth duration path =
      (recoveryCircuit P).depth duration path.2 := by
  change (outputAllocation P).depth duration path.1 +
    (recoveryCircuit P).depth duration path.2 = _
  rw [outputAllocation_depth, Nat.zero_add]

/-- The retained tail's resident peak is the maximum of allocation and recovery. -/
public theorem retainedRecovery_peakResidentSpace (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakResidentSpace path =
      SpacePool.max (outputContext P).residentSpace
        ((recoveryCircuit P).peakResidentSpace path.2) := by
  exact (Circuit.peakResidentSpace_seq (outputAllocation P) (recoveryCircuit P) path).trans
    (congrArg (fun first => SpacePool.max first
      ((recoveryCircuit P).peakResidentSpace path.2))
        (outputAllocation_peakResidentSpace P path.1))

/-- The retained tail's auxiliary peak is the maximum of allocation and recovery. -/
public theorem retainedRecovery_peakAuxiliarySpace (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakAuxiliarySpace path =
      SpacePool.max (outputContext P).auxiliarySpace
        ((recoveryCircuit P).peakAuxiliarySpace path.2) := by
  exact (Circuit.peakAuxiliarySpace_seq (outputAllocation P) (recoveryCircuit P) path).trans
    (congrArg (fun first => SpacePool.max first
      ((recoveryCircuit P).peakAuxiliarySpace path.2))
        (outputAllocation_peakAuxiliarySpace P path.1))

/-- Canonical all-order sampling followed by the actual checked recovery tail. -/
@[expose] public def code (P : KnownOrderProblem G) :
    Circuit (OrderExecution.model P) OrderExecution.pre (outputContext P) :=
  .seq (OrderBatch.code P (sampleCount P) (OrderExecution.canonicalExpansion P))
    (retainedRecovery P)

/-- Complete executable endpoint returning one optional residue word. -/
@[expose] public def run (P : KnownOrderProblem G) :
    AlgorithmRun (OrderExecution.model P) OrderExecution.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  code := code P
  output := Output.all (outputContext P)
    (.read (.storage (outputRef P).toCStorageRef))

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
