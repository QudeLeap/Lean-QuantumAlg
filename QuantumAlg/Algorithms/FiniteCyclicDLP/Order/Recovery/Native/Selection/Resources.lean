/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Resources of checked recovery from a retained sample batch

Every retained sample runs full raw recovery, abstract group verification and
the first-accepted update.  Later samples still execute after an earlier
success.  One actual optional-result pack follows the chronological loop.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- Independent duration allowance of one first-accepted selector step. -/
public def selectionDepthLimit
    (duration : Resource.Event (OrderExecution.model P) → Nat) : Nat :=
  duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P) (.bit .not))) +
    duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P) (.bit .and))) +
    (duration (.classicalOperation
        (BitWord.selectedCoordinate (execution := OrderExecution.model P)
          (.wordUnary .copy (OrderPreparation.width P)))) +
      duration (.classicalOperation
        (BitWord.selectedCoordinate (execution := OrderExecution.model P) (.bit .copy))))

private theorem selector_depth
    (inputs : FirstAccepted.Inputs ctx (OrderPreparation.width P))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (FirstAccepted.circuit
      (model := OrderExecution.model P) inputs refs).Path) :
    (FirstAccepted.circuit (model := OrderExecution.model P) inputs refs).depth duration path ≤
      selectionDepthLimit P duration := by
  rw [FirstAccepted.firstAccepted_depth]
  unfold selectionDepthLimit
  apply Nat.add_le_add_left
  split <;> omega

/-- Independent events for every attempt and selector, followed by one pack. -/
public def recoveryEnvelope
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat) : ResourcePool (OrderExecution.model P) :=
  ResourcePool.scale count
      (attemptEnvelope P spec +
        FirstAccepted.nativeEnvelope (OrderExecution.model P) (OrderPreparation.width P)) +
    ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P)
        (.nominalEncoding (.packOption (OrderPreparation.width P)))))

/-- Every retained sample reserves two group operations per candidate bit. -/
@[simp] public theorem recoveryEnvelope_groupOperation_count
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat) :
    ResourcePool.count (groupOperationEvent P) (recoveryEnvelope P spec count) =
      count * (2 * OrderPreparation.width P) := by
  have selectorZero :
      ResourcePool.count (groupOperationEvent P)
        (FirstAccepted.nativeEnvelope (OrderExecution.model P)
          (OrderPreparation.width P)) = 0 := by
    simp [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents,
      FirstAccepted.copyEvents, groupOperationEvent,
      ResourcePool.ofList, ResourcePool.count]
  have packZero :
      ResourcePool.count (groupOperationEvent P)
        (ResourcePool.singleton (.classicalOperation
          (BitWord.selectedCoordinate (execution := OrderExecution.model P)
            (.nominalEncoding (.packOption (OrderPreparation.width P)))))) = 0 := by
    simp [groupOperationEvent, ResourcePool.singleton, ResourcePool.count]
  unfold recoveryEnvelope
  rw [ResourcePool.count_add, ResourcePool.count_scale, ResourcePool.count_add,
    attemptEnvelope_groupOperation_count, selectorZero, add_zero, packZero]
  rfl

/-- The complete recovery tail contains no quantum gate or quantum-oracle event. -/
theorem recoveryEnvelope_count_nonclassical
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat) (event : Resource.Event (OrderExecution.model P))
    (outsideOperation : ∀ operation, event ≠ .classicalOperation operation)
    (outsideQuery : ∀ query, event ≠ .classicalQuery query) :
    ResourcePool.count event (recoveryEnvelope P spec count) = 0 := by
  have selectorZero :
      ResourcePool.count event
        (FirstAccepted.nativeEnvelope (OrderExecution.model P)
          (OrderPreparation.width P)) = 0 := by
    simp [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents,
      FirstAccepted.copyEvents, ResourcePool.ofList, ResourcePool.count,
      outsideOperation]
  have packZero :
      ResourcePool.count event
        (ResourcePool.singleton (.classicalOperation
          (BitWord.selectedCoordinate (execution := OrderExecution.model P)
            (.nominalEncoding (.packOption (OrderPreparation.width P)))))) = 0 :=
    ResourcePool.count_singleton_of_ne (outsideOperation _) 1
  unfold recoveryEnvelope
  rw [ResourcePool.count_add, ResourcePool.count_scale, ResourcePool.count_add,
    attemptEnvelope_count_nonclassical P spec event outsideOperation outsideQuery,
    selectorZero, add_zero, mul_zero, packZero]

/-- Serial dependency allowance for every attempt, selector and final pack. -/
public def recoveryDepthLimit
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat) (duration : Resource.Event (OrderExecution.model P) → Nat) : Nat :=
  count * (attemptDepthLimit P spec duration + selectionDepthLimit P duration) +
    duration (.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P)
        (.nominalEncoding (.packOption (OrderPreparation.width P)))))

/-- One attempt workspace is reused across all retained samples. -/
public def selectionAttemptSpace : SpacePool .quantum :=
  ((attemptShapes (OrderPreparation.width P)).map SpacePool.ofShape).sum +
    attemptActiveSpace P 0

/-- Four persistent selector cells enclose the reused attempt maximum. -/
public def recoveryScratchSpace : SpacePool .quantum :=
  ((selectorShapes (OrderPreparation.width P)).map SpacePool.ofShape).sum +
    selectionAttemptSpace P

private theorem attempt_pool
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (path : (selectAttempt P spec input refs).Path) :
    (selectAttempt P spec input refs).resourcePool path ≤
      attemptEnvelope P spec +
        FirstAccepted.nativeEnvelope (OrderExecution.model P) (OrderPreparation.width P) := by
  unfold selectAttempt at path ⊢
  exact withAttempt_pool_le P spec input _
    (FirstAccepted.nativeEnvelope (OrderExecution.model P) (OrderPreparation.width P))
    (fun candidate accepted transport =>
      FirstAccepted.firstAccepted_pool_le
        (model := OrderExecution.model P) ⟨accepted, candidate⟩ (liftSelector refs transport)) path

private theorem attempt_depth
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (selectAttempt P spec input refs).Path) :
    (selectAttempt P spec input refs).depth duration path ≤
      attemptDepthLimit P spec duration + selectionDepthLimit P duration := by
  unfold selectAttempt at path ⊢
  exact withAttempt_depth_le P spec input _ duration (selectionDepthLimit P duration)
    (fun candidate accepted transport => selector_depth P ⟨accepted, candidate⟩
      (liftSelector refs transport) duration) path

private theorem attempt_resident
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (path : (selectAttempt P spec input refs).Path) :
    (selectAttempt P spec input refs).peakResidentSpace path ≤
      selectionAttemptSpace P + ctx.residentSpace := by
  unfold selectAttempt at path ⊢
  unfold selectionAttemptSpace
  exact withAttempt_resident_le P spec input _ 0 (by
    intro inner candidate accepted transport selected
    simpa only [zero_add] using FirstAccepted.firstAccepted_resident_le
      (model := OrderExecution.model P) ⟨accepted, candidate⟩
        (liftSelector refs transport) selected) path

private theorem attempt_auxiliary
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (path : (selectAttempt P spec input refs).Path) :
    (selectAttempt P spec input refs).peakAuxiliarySpace path ≤
      selectionAttemptSpace P + ctx.auxiliarySpace := by
  unfold selectAttempt at path ⊢
  unfold selectionAttemptSpace
  exact withAttempt_auxiliary_le P spec input _ 0 (by
    intro inner candidate accepted transport selected
    simpa only [zero_add] using FirstAccepted.firstAccepted_auxiliary_le
      (model := OrderExecution.model P) ⟨accepted, candidate⟩
        (liftSelector refs transport) selected) path

variable
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (output : CWriteRef ctx (.option (.unsignedWord (OrderPreparation.width P))))

/-- The actual loop trace is followed by the one real pack event. -/
public theorem recoveryBody_eventTrace
    (path : (recoveryBody P spec count samples refs output).Path) :
    (recoveryBody P spec count samples refs output).eventTrace path =
      (selectionLoop P spec count samples refs).eventTrace path.1 ++
        [.classicalOperation
          (BitWord.selectedCoordinate (execution := OrderExecution.model P)
            (.nominalEncoding (.packOption (OrderPreparation.width P))))] := by
  unfold recoveryBody at path ⊢
  rfl

/-- The complete loop and final pack meet their independent allowance. -/
public theorem recoveryBody_pool_le
    (path : (recoveryBody P spec count samples refs output).Path) :
    (recoveryBody P spec count samples refs output).resourcePool path ≤
      recoveryEnvelope P spec count := by
  unfold recoveryBody at path ⊢
  rw [Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append]
  exact add_le_add (Circuit.forRange_pool_le count _ _
    (fun index => attempt_pool P spec (samples index) refs) path.1) le_rfl

/-- Arbitrary durations charge every actual attempt before the final pack. -/
public theorem recoveryBody_depth_le
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (recoveryBody P spec count samples refs output).Path) :
    (recoveryBody P spec count samples refs output).depth duration path ≤
      recoveryDepthLimit P spec count duration := by
  unfold recoveryBody at path ⊢
  have loopBound := Circuit.forRange_depth_le_sum count
    (fun index => selectAttempt P spec (samples index) refs) duration
    (fun _ => attemptDepthLimit P spec duration + selectionDepthLimit P duration)
    (fun index => attempt_depth P spec (samples index) refs duration) path.1
  have loop : (selectionLoop P spec count samples refs).depth duration path.1 ≤
      count * (attemptDepthLimit P spec duration + selectionDepthLimit P duration) := by
    simpa only [selectionLoop, Finset.sum_const, Finset.card_fin, smul_eq_mul] using loopBound
  exact Nat.add_le_add loop le_rfl

private theorem pack_resident
    (path : (BitWord.instruction (execution := OrderExecution.model P)
      (selectionPack refs output)).Path) :
    (BitWord.instruction (execution := OrderExecution.model P)
      (selectionPack refs output)).peakResidentSpace path ≤ ctx.residentSpace :=
  le_of_eq (Circuit.peakResidentSpace_classical _ path)

private theorem pack_auxiliary
    (path : (BitWord.instruction (execution := OrderExecution.model P)
      (selectionPack refs output)).Path) :
    (BitWord.instruction (execution := OrderExecution.model P)
      (selectionPack refs output)).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  le_of_eq (Circuit.peakAuxiliarySpace_classical _ path)

/-- The complete loop reuses one attempt workspace and retains the caller context. -/
public theorem recoveryBody_resident_le
    (path : (recoveryBody P spec count samples refs output).Path) :
    (recoveryBody P spec count samples refs output).peakResidentSpace path ≤
      selectionAttemptSpace P + ctx.residentSpace := by
  unfold recoveryBody at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    (Circuit.forRange_resident_le count _ _ (le_add_of_nonneg_left zero_le)
      (fun index => attempt_resident P spec (samples index) refs) path.1)
    ((pack_resident P refs output path.2).trans
      (le_add_of_nonneg_left zero_le))

/-- The same reuse principle bounds all auxiliary roles. -/
public theorem recoveryBody_auxiliary_le
    (path : (recoveryBody P spec count samples refs output).Path) :
    (recoveryBody P spec count samples refs output).peakAuxiliarySpace path ≤
      selectionAttemptSpace P + ctx.auxiliarySpace := by
  unfold recoveryBody at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    (Circuit.forRange_auxiliary_le count _ _ (le_add_of_nonneg_left zero_le)
      (fun index => attempt_auxiliary P spec (samples index) refs) path.1)
    ((pack_auxiliary P refs output path.2).trans
      (le_add_of_nonneg_left zero_le))

omit refs in
/-- Selector allocation preserves the complete event allowance. -/
public theorem recoveryInto_pool_le
    (path : (recoveryInto P spec count samples output).Path) :
    (recoveryInto P spec count samples output).resourcePool path ≤
      recoveryEnvelope P spec count := by
  unfold recoveryInto at path ⊢
  apply withCellsFrom_pool_le
  intro inner cells distinct transport separated selected
  exact recoveryBody_pool_le P spec count
    (fun index => transport.liftInput (samples index))
    (selectorRefs cells) (transport.liftWrite output) selected

omit refs in
/-- Selector allocation preserves the complete dependency allowance. -/
public theorem recoveryInto_depth_le
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (recoveryInto P spec count samples output).Path) :
    (recoveryInto P spec count samples output).depth duration path ≤
      recoveryDepthLimit P spec count duration := by
  unfold recoveryInto at path ⊢
  apply withCellsFrom_depth_le
  intro inner cells distinct transport separated selected
  exact recoveryBody_depth_le P spec count
    (fun index => transport.liftInput (samples index))
    (selectorRefs cells) (transport.liftWrite output) duration selected

omit refs in
/-- Once-allocated selector cells enclose the reused resident attempt maximum. -/
public theorem recoveryInto_resident_le
    (path : (recoveryInto P spec count samples output).Path) :
    (recoveryInto P spec count samples output).peakResidentSpace path ≤
      recoveryScratchSpace P + ctx.residentSpace := by
  unfold recoveryInto at path ⊢
  unfold recoveryScratchSpace
  exact withCellsFrom_resident_le (model := OrderExecution.model P) (Transport.id ctx)
    (selectorShapes (OrderPreparation.width P)) _ (selectionAttemptSpace P) (by
      intro inner cells distinct transport separated selected
      exact recoveryBody_resident_le P spec count
        (fun index => transport.liftInput (samples index))
        (selectorRefs cells) (transport.liftWrite output) selected) path

omit refs in
/-- The same selector scope encloses the reused auxiliary maximum. -/
public theorem recoveryInto_auxiliary_le
    (path : (recoveryInto P spec count samples output).Path) :
    (recoveryInto P spec count samples output).peakAuxiliarySpace path ≤
      recoveryScratchSpace P + ctx.auxiliarySpace := by
  unfold recoveryInto at path ⊢
  unfold recoveryScratchSpace
  exact withCellsFrom_auxiliary_le (model := OrderExecution.model P) (Transport.id ctx)
    (selectorShapes (OrderPreparation.width P)) _ (selectionAttemptSpace P) (by
      intro inner cells distinct transport separated selected
      exact recoveryBody_auxiliary_le P spec count
        (fun index => transport.liftInput (samples index))
        (selectorRefs cells) (transport.liftWrite output) selected) path

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
