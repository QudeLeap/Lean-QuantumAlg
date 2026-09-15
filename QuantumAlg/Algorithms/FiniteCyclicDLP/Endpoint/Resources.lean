/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Independent resources of the complete actual finite-cyclic endpoint

The original fixed sample count pays for one preparation, every literal
member and measurement, and all later complete-bank resets. The one result
allocation follows sampling and precedes every complete classical recovery
attempt and the final selector pack. Declared group calls stay in the native
allowance. Storage includes all samples, the bank, result and borrowed target;
only the lexical recovery workspace is reused across attempts.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Original independent sampling and complete call-counted recovery allowances. -/
def eventBudget (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    ResourcePool .quantum :=
  GateLevelAttempt.Native.Batch.eventBudget P B A.ux (retryCount P) +
    CallCountedRecovery.Native.recoveryEnvelope (recoveryParameters P B A) (retryCount P)

/-- Actual reset paths use one selected correction, followed by the full recovery allowance. -/
def eventCountLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) : Nat :=
  GateLevelAttempt.Native.Batch.eventCountLimit P B (retryCount P) +
    (CallCountedRecovery.Native.recoveryEnvelope (recoveryParameters P B A) (retryCount P)).card

/-- Original parallel quantum depth followed by the complete serial recovery dependency bound. -/
def unitDepthLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) : Nat :=
  GateLevelAttempt.Native.Batch.depthLimit P B (retryCount P) +
    CallCountedRecovery.Native.recoveryDepthLimit (recoveryParameters P B A)
      (retryCount P) (fun _ => 1)

/-- A conservative independent bound for arbitrary durations, including declared group calls. -/
def weightedDepthLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (duration : Resource.Event .quantum → Nat) : Nat :=
  ResourcePool.weightedCount duration (eventBudget P B A)

/-- The actual optional result remains live after all samples have been measured. -/
def resultSpace (P : KnownOrderProblem G) : SpacePool .quantum :=
  SpacePool.ofShape (.option (.unsignedWord (orderWidth P)))

/-- One maximum recovery workspace, the result, every sample and the complete original input. -/
def residentBudget (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) : SpacePool .quantum :=
  CallCountedRecovery.Native.recoveryScratchSpace (recoveryParameters P B A) +
    (resultSpace P +
      (GateLevelAttempt.Native.Batch.samplingSpace P (retryCount P) + (pre P).residentSpace))

/-- The same complete owned workspace, with the original caller's auxiliary roles. -/
def auxiliaryBudget (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) : SpacePool .quantum :=
  CallCountedRecovery.Native.recoveryScratchSpace (recoveryParameters P B A) +
    (resultSpace P +
      (GateLevelAttempt.Native.Batch.samplingSpace P (retryCount P) + (pre P).auxiliarySpace))

/-- The actual output context contains the retained result, all samples, bank and caller. -/
theorem finiteCyclic_outputContext_residentSpace (P : KnownOrderProblem G) :
    (outputContext P).residentSpace = resultSpace P +
      (GateLevelAttempt.Native.Batch.samplingSpace P (retryCount P) + (pre P).residentSpace) := by
  rw [outputContext, RuntimeCtx.residentSpace_addRetained]
  change resultSpace P + (sampledContext P).residentSpace = _
  rw [sampledContext, GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_context_residentSpace]

/-- The actual output context retains every newly allocated entry in its auxiliary accounting. -/
theorem finiteCyclic_outputContext_auxiliarySpace (P : KnownOrderProblem G) :
    (outputContext P).auxiliarySpace = resultSpace P +
      (GateLevelAttempt.Native.Batch.samplingSpace P (retryCount P) + (pre P).auxiliarySpace) := by
  rw [outputContext, RuntimeCtx.auxiliarySpace_addRetained]
  change resultSpace P + (sampledContext P).auxiliarySpace = _
  rw [sampledContext, GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_context_auxiliarySpace]

variable (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)

/-- All actual sampling, reset, recovery and final pack events meet the independent budget. -/
theorem finiteCyclic_run_pool_le (path : (run P B A).code.Path) :
    (run P B A).code.resourcePool path ≤ eventBudget P B A := by
  change ResourcePool.ofList
    ((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P) P
      (retryCount P) B A.ux).eventTrace path.1 ++
        ([] ++ (recoveryCircuit P B A).eventTrace path.2.2)) ≤ _
  rw [List.nil_append, ResourcePool.ofList_append]
  exact add_le_add
    (GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_run_pool_le
      (pre P) (input_quantumWires P) P (retryCount P) B A.ux path.1)
    (CallCountedRecovery.Native.groupRecoveryInto_pool_le (recoveryParameters P B A)
      (retryCount P) (retainedSample P) (retainedTarget P) (outputRef P) path.2.2)

/-- The count uses actual reset paths and still charges every complete classical attempt. -/
theorem finiteCyclic_run_eventCount_le (path : (run P B A).code.Path) :
    ((run P B A).code.eventTrace path).length ≤ eventCountLimit P B A := by
  change ((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P) P
    (retryCount P) B A.ux).eventTrace path.1 ++
      ([] ++ (recoveryCircuit P B A).eventTrace path.2.2)).length ≤ _
  rw [List.nil_append, List.length_append]
  exact Nat.add_le_add
    (GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_run_eventCount
      (pre P) (input_quantumWires P) P (retryCount P) B A.ux path.1).le
    (Multiset.card_le_card
      (CallCountedRecovery.Native.groupRecoveryInto_pool_le (recoveryParameters P B A)
        (retryCount P) (retainedSample P) (retainedTarget P) (outputRef P) path.2.2))

/-- Unit depth retains the original parallel member bound before serial classical recovery. -/
theorem finiteCyclic_run_unitDepth_le (path : (run P B A).code.Path) :
    (run P B A).code.depth (fun _ => 1) path ≤ unitDepthLimit P B A := by
  change (GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P) P
    (retryCount P) B A.ux).depth (fun _ => 1) path.1 +
      (0 + (recoveryCircuit P B A).depth (fun _ => 1) path.2.2) ≤ _
  rw [zero_add]
  exact Nat.add_le_add
    (GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_run_depth_le
      (pre P) (input_quantumWires P) P (retryCount P) B A.ux path.1)
    (CallCountedRecovery.Native.groupRecoveryInto_depth_le (recoveryParameters P B A)
      (retryCount P) (retainedSample P) (retainedTarget P) (outputRef P) (fun _ => 1) path.2.2)

/-- Every duration assignment bounds the same actual dependency path by its independent work. -/
theorem finiteCyclic_run_weightedDepth_le (duration : Resource.Event .quantum → Nat)
    (path : (run P B A).code.Path) :
    (run P B A).code.depth duration path ≤ weightedDepthLimit P B A duration :=
  Circuit.depth_le_weightedCount_of_pool_le (run P B A).code duration
    (eventBudget P B A) path (finiteCyclic_run_pool_le P B A path)

private theorem retain_resident {ctx : RuntimeCtx .quantum}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (path : (Circuit.retain ctx key shape fresh).Path) :
    (Circuit.retain ctx key shape fresh).peakResidentSpace path ≤
      (ctx.addRetained key shape fresh).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  change frame ∈ [ctx, ctx.addRetained key shape fresh] at present
  rcases List.mem_cons.mp present with rfl | later
  · rw [RuntimeCtx.residentSpace_addRetained]
    exact le_add_of_nonneg_left zero_le
  · have same := List.mem_singleton.mp later
    subst frame
    exact le_rfl

private theorem retain_auxiliary {ctx : RuntimeCtx .quantum}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (path : (Circuit.retain ctx key shape fresh).Path) :
    (Circuit.retain ctx key shape fresh).peakAuxiliarySpace path ≤
      (ctx.addRetained key shape fresh).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  change frame ∈ [ctx, ctx.addRetained key shape fresh] at present
  rcases List.mem_cons.mp present with rfl | later
  · rw [RuntimeCtx.auxiliarySpace_addRetained]
    exact le_add_of_nonneg_left zero_le
  · have same := List.mem_singleton.mp later
    subst frame
    exact le_rfl

private theorem retainedRecovery_resident
    (path : (retainedRecovery P B A).Path) :
    (retainedRecovery P B A).peakResidentSpace path ≤ residentBudget P B A := by
  refine (Circuit.peakResidentSpace_seq
    (Circuit.retain (sampledContext P) (outputKey P)
      (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P))
    (recoveryCircuit P B A) path).trans_le ?_
  have retained := retain_resident (outputKey P) (.option (.unsignedWord (orderWidth P)))
    (outputKey_fresh P) path.1
  have tail := CallCountedRecovery.Native.groupRecoveryInto_resident_le
    (recoveryParameters P B A) (retryCount P) (retainedSample P) (retainedTarget P)
    (outputRef P) path.2
  have same := finiteCyclic_outputContext_residentSpace P
  unfold residentBudget
  rw [← same]
  exact SpacePool.max_le (retained.trans (le_add_of_nonneg_left zero_le)) tail

private theorem retainedRecovery_auxiliary
    (path : (retainedRecovery P B A).Path) :
    (retainedRecovery P B A).peakAuxiliarySpace path ≤ auxiliaryBudget P B A := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Circuit.retain (sampledContext P) (outputKey P)
      (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P))
    (recoveryCircuit P B A) path).trans_le ?_
  have retained := retain_auxiliary (outputKey P) (.option (.unsignedWord (orderWidth P)))
    (outputKey_fresh P) path.1
  have tail := CallCountedRecovery.Native.groupRecoveryInto_auxiliary_le
    (recoveryParameters P B A) (retryCount P) (retainedSample P) (retainedTarget P)
    (outputRef P) path.2
  have same := finiteCyclic_outputContext_auxiliarySpace P
  unfold auxiliaryBudget
  rw [← same]
  exact SpacePool.max_le (retained.trans (le_add_of_nonneg_left zero_le)) tail

/-- The full actual resident peak includes all samples, the original bank and real result. -/
theorem finiteCyclic_run_resident_le (path : (run P B A).code.Path) :
    (run P B A).code.peakResidentSpace path ≤ residentBudget P B A := by
  refine (Circuit.peakResidentSpace_seq
    (GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P) P
      (retryCount P) B A.ux) (retainedRecovery P B A) path).trans_le ?_
  apply SpacePool.max_le _ (retainedRecovery_resident P B A path.2)
  refine (GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_run_resident
    (pre P) (input_quantumWires P) P (retryCount P) B A.ux path.1).trans_le ?_
  exact (le_add_of_nonneg_left (show 0 ≤ resultSpace P from zero_le)).trans
    (le_add_of_nonneg_left zero_le)

/-- The full actual auxiliary peak reuses one recovery workspace and retains all owned output. -/
theorem finiteCyclic_run_auxiliary_le (path : (run P B A).code.Path) :
    (run P B A).code.peakAuxiliarySpace path ≤ auxiliaryBudget P B A := by
  refine (Circuit.peakAuxiliarySpace_seq
    (GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P) P
      (retryCount P) B A.ux) (retainedRecovery P B A) path).trans_le ?_
  apply SpacePool.max_le _ (retainedRecovery_auxiliary P B A path.2)
  refine (GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_run_auxiliary
    (pre P) (input_quantumWires P) P (retryCount P) B A.ux path.1).trans_le ?_
  exact (le_add_of_nonneg_left (show 0 ≤ resultSpace P from zero_le)).trans
    (le_add_of_nonneg_left zero_le)

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
