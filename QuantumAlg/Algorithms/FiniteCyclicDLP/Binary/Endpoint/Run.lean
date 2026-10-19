/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Amplification
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
# Complete binary single-bank finite-cyclic DLP run

The full-family retry count drives the actual sequential binary sampler. One
retained optional word is then written by either the certain order-one routine
or the original checked recovery and ambient-group verification tail. The
last quantum round physically resets its bank before this classical tail
[Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

open Execution

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Number of actual samples used by the two-thirds amplification. -/
public abbrev sampleCount (P : KnownOrderProblem G) : Nat :=
  Binary.sampleCount P

/-- Complete post-sampling context before the result is allocated. -/
public abbrev sampledContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  Reusable.context P (sampleCount P)

/-- Fresh key of the single retained optional result. -/
@[expose] public def outputKey (P : KnownOrderProblem G) : StorageKey :=
  (sampledContext P).canonicalFreshKey

omit [Fintype G] in
public lemma binaryEndpoint_outputKey_fresh (P : KnownOrderProblem G) :
    outputKey P ∉ (sampledContext P).keys :=
  RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampledContext P)

/-- All retained samples, the one restored qubit bank, reset scratch and final optional word
  remain live. -/
@[expose] public def outputContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  (sampledContext P).addRetained (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)

/-- Writable destination of the one actual endpoint result. -/
@[expose] public def outputRef (P : KnownOrderProblem G) :
    CWriteRef (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) :=
  CWriteRef.retainedHead (sampledContext P) (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)

/-- One retained sample transported through result allocation. -/
@[expose] public def retainedSample (P : KnownOrderProblem G) (slot : Fin (sampleCount P)) :
    CInputRef (outputContext P)
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)) :=
  (Reusable.sampleInput P slot).underRetained (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)

/-- The nontrivial modular recovery specification follows solely from the known order. -/
@[expose] public def recoverySpec (P : KnownOrderProblem G) (nontrivial : P.order ≠ 1) :
    ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P) :=
  Canonical.resourceModulusSpec P (by
    have positive := P.order_pos
    omega)

/-- Order one returns zero certainly; every other positive order executes the
complete raw recovery, abstract group power and target comparison. -/
@[expose] public def recoveryCircuit (P : KnownOrderProblem G) :
    Circuit (Reusable.model P) (outputContext P) (outputContext P) :=
  if trivial : P.order = 1 then
    ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto (outputRef P)
  else
    OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
      trivial) (sampleCount P)
      (retainedSample P) (outputRef P)

/-- Order one selects the literal zero-writing recovery branch. -/
public lemma binaryEndpoint_recoveryCircuit_order_one (P : KnownOrderProblem G)
    (trivial : P.order = 1) :
    recoveryCircuit P =
      ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto (outputRef P) := by
  exact dif_pos trivial

/-- Every nontrivial positive order selects checked native recovery. -/
public lemma binaryEndpoint_recoveryCircuit_nontrivial (P : KnownOrderProblem G)
    (nontrivial : P.order ≠ 1) :
    recoveryCircuit P =
      OrderRecovery.Native.recoveryInto (oracles := Binary.Oracle.model P) P (recoverySpec P
        nontrivial) (sampleCount P)
        (retainedSample P) (outputRef P) := by
  exact dif_neg nontrivial

/-- Allocate the result cell behind the abstract endpoint context boundary. -/
public def outputAllocation (P : KnownOrderProblem G) :
    Circuit (Reusable.model P) (sampledContext P) (outputContext P) :=
  .retain (model := Reusable.model P) (sampledContext P) (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)

/-- The allocation instruction has its unique execution path. -/
public def outputAllocationPath (P : KnownOrderProblem G) :
    (outputAllocation P).Path := ()

/-- Classical record produced by the result-cell allocation. -/
public def retainedEntry (P : KnownOrderProblem G) {History : Type}
    (entry : Store (sampledContext P) ×
      ((Reusable.model P).HiddenState × History)) :
    Store (outputContext P) ×
      ((Reusable.model P).HiddenState × (History × (outputAllocation P).Path)) :=
    (entry.1.pushRetained (outputKey P)
      (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P),
        (entry.2.1, (entry.2.2, outputAllocationPath P)))

/-- Actual result allocation preserves the hidden service state and appends one path unit. -/
public def retainedState (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((Reusable.model P).HiddenState × History)) :
    State (outputContext P) Reference
      ((Reusable.model P).HiddenState × (History × (outputAllocation P).Path)) :=
  state.mapClassical (retainedEntry P)

/-- Allocating a result cell preserves normalization. -/
public lemma binaryEndpoint_retainedState_normalized (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((Reusable.model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    (retainedState P state).IsNormalized := by
  exact state.mapClassical_normalized normalized (retainedEntry P)

/-- Result allocation pushes forward only the finite classical record law. -/
public lemma binaryEndpoint_retainedState_toPMF (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((Reusable.model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    (retainedState P state).toPMF (binaryEndpoint_retainedState_normalized P state normalized) =
      (state.toPMF normalized).map (retainedEntry P) := by
  exact ExecutionState.toPMF_mapClassical state normalized (retainedEntry P)

/-- Result allocation preserves every sample read under its retained reference. -/
public lemma binaryEndpoint_retainedEntry_read_sample (P : KnownOrderProblem G) {History : Type}
    (entry : Store (sampledContext P) ×
      ((Reusable.model P).HiddenState × History))
    (index : Fin (sampleCount P)) :
    (retainedEntry P entry).1.read (retainedSample P index) =
      entry.1.read (Reusable.sampleInput P index) := by
  exact Store.read_pushRetained_underRetained entry.1 (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)
      (Reusable.sampleInput P index)

/-- The literal retained-cell instruction executes as `retainedState`. -/
public lemma binaryEndpoint_outputRetain_execute (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((Reusable.model P).HiddenState × History)) :
    (outputAllocation P).execute
      (Reusable.sourceEnvironment P) Reference state = retainedState P state := by
  unfold outputAllocation retainedState retainedEntry outputAllocationPath
  refine (Circuit.execute_retain (environment := Reusable.sourceEnvironment P)
      (model := Reusable.model P)
      (ctx := sampledContext P) (Reference := Reference) state (outputKey P)
        (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh
          P)).trans ?_
  exact ExecutionState.executionState_mapClassical_congr state rfl

/-- Result allocation emits no native event. -/
public lemma binaryEndpoint_outputAllocation_eventTrace (P : KnownOrderProblem G)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).eventTrace path = [] := by
  unfold outputAllocation
  rfl

/-- Result allocation adds no dependency duration. -/
public lemma binaryEndpoint_outputAllocation_depth (P : KnownOrderProblem G)
    (duration : Resource.Event (Reusable.model P) → Nat)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).depth duration path = 0 := by
  unfold outputAllocation
  rfl

/-- Allocation visits exactly the original and retained resident contexts. -/
public lemma binaryEndpoint_outputAllocation_peakResidentSpace (P : KnownOrderProblem G)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).peakResidentSpace path =
      (outputContext P).residentSpace := by
  unfold outputAllocation
  exact Circuit.peakResidentSpace_retain _ _ _ path

/-- Allocation visits exactly the original and retained auxiliary contexts. -/
public lemma binaryEndpoint_outputAllocation_peakAuxiliarySpace (P : KnownOrderProblem G)
    (path : (outputAllocation P).Path) :
    (outputAllocation P).peakAuxiliarySpace path =
      (outputContext P).auxiliarySpace := by
  unfold outputAllocation
  exact Circuit.peakAuxiliarySpace_retain _ _ _ path

/-- Allocate the result only after every quantum sample has completed. -/
public abbrev retainedRecovery (P : KnownOrderProblem G) :
    Circuit (Reusable.model P) (sampledContext P) (outputContext P) :=
  .seq (outputAllocation P) (recoveryCircuit P)

/-- Result retention is the literal allocation followed by the selected recovery branch. -/
public lemma binaryEndpoint_retainedRecovery_sequence (P : KnownOrderProblem G) :
    retainedRecovery P =
      .seq (outputAllocation P) (recoveryCircuit P) := rfl

/-- Allocating the result emits no resource event before recovery. -/
public lemma binaryEndpoint_retainedRecovery_resourcePool (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).resourcePool path =
      (recoveryCircuit P).resourcePool path.2 := by
  change ResourcePool.ofList
    ((outputAllocation P).eventTrace path.1 ++
      (recoveryCircuit P).eventTrace path.2) = _
  rw [binaryEndpoint_outputAllocation_eventTrace, List.nil_append]
  rfl

/-- Allocating the result adds no dependency duration before recovery. -/
public lemma binaryEndpoint_retainedRecovery_depth (P : KnownOrderProblem G)
    (duration : Resource.Event (Reusable.model P) → Nat)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).depth duration path =
      (recoveryCircuit P).depth duration path.2 := by
  change (outputAllocation P).depth duration path.1 +
    (recoveryCircuit P).depth duration path.2 = _
  rw [binaryEndpoint_outputAllocation_depth, Nat.zero_add]

/-- The retained tail's resident peak is the maximum of allocation and recovery. -/
public lemma binaryEndpoint_retainedRecovery_peakResidentSpace (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakResidentSpace path =
      SpacePool.max (outputContext P).residentSpace
        ((recoveryCircuit P).peakResidentSpace path.2) := by
  exact (Circuit.peakResidentSpace_seq (outputAllocation P) (recoveryCircuit P) path).trans
    (congrArg (fun first => SpacePool.max first
      ((recoveryCircuit P).peakResidentSpace path.2))
        (binaryEndpoint_outputAllocation_peakResidentSpace P path.1))

/-- The retained tail's auxiliary peak is the maximum of allocation and recovery. -/
public lemma binaryEndpoint_retainedRecovery_peakAuxiliarySpace (P : KnownOrderProblem G)
    (path : (retainedRecovery P).Path) :
    (retainedRecovery P).peakAuxiliarySpace path =
      SpacePool.max (outputContext P).auxiliarySpace
        ((recoveryCircuit P).peakAuxiliarySpace path.2) := by
  exact (Circuit.peakAuxiliarySpace_seq (outputAllocation P) (recoveryCircuit P) path).trans
    (congrArg (fun first => SpacePool.max first
      ((recoveryCircuit P).peakAuxiliarySpace path.2))
        (binaryEndpoint_outputAllocation_peakAuxiliarySpace P path.1))

/-- Canonical all-order sampling followed by the actual checked recovery tail. -/
@[expose] public def code (P : KnownOrderProblem G) :
    Circuit (Reusable.model P) Reusable.pre (outputContext P) :=
  .seq (Reusable.code P (sampleCount P) (OrderExecution.canonicalExpansion P))
    (retainedRecovery P)

/-- Complete executable endpoint returning one optional residue word. -/
@[expose] public def run (P : KnownOrderProblem G) :
    AlgorithmRun (Reusable.model P) Reusable.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  code := code P
  output := Output.all (outputContext P)
    (.read (.storage (outputRef P).toCStorageRef))

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
