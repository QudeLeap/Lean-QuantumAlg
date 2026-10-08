/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power.Resources
public import
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Coordinates
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources
import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Query and native-operation resources of one checked recovery attempt

Raw integer recovery retains its actual default-model expansion. Explicit
reset, group operations and equality remain separate declared-query
coordinates, followed by two actual native conjunctions.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- The two native conjunction events that combine one attempt's acceptance bits. -/
@[expose] public def acceptanceEvents : List (Resource.Event (OrderExecution.model P)) :=
  [.classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P) (.bit .and)),
    .classicalOperation
      (BitWord.selectedCoordinate (execution := OrderExecution.model P) (.bit .and))]

private theorem acceptanceSuffix_eventTrace {width : Nat}
    (refs : AttemptRefs ctx width) (path : (acceptanceSuffix P refs).Path) :
    (acceptanceSuffix P refs).eventTrace path = acceptanceEvents P := rfl

private theorem acceptanceSuffix_depth {width : Nat}
    (refs : AttemptRefs ctx width)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (acceptanceSuffix P refs).Path) :
    (acceptanceSuffix P refs).depth duration path =
      ((acceptanceEvents P).map duration).sum := rfl

/-- An independent resource allowance for one complete checked recovery attempt. -/
@[expose] public def attemptEnvelope
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P)) :
    ResourcePool (OrderExecution.model P) :=
  RawRecovery.Native.singleExposureEnvelope (OrderExecution.model P) spec +
    (powerCheckEnvelope P (OrderPreparation.width P) +
      ResourcePool.ofList (acceptanceEvents P))

/-- One checked attempt reserves exactly two group operations per candidate bit. -/
@[simp] public theorem attemptEnvelope_groupOperation_count
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P)) :
    ResourcePool.count (groupOperationEvent P) (attemptEnvelope P spec) =
      2 * OrderPreparation.width P := by
  simp only [attemptEnvelope, ResourcePool.count_add,
    RawRecovery.Native.singleExposureEnvelope_count_nonclassical
      (groupOperationEvent P) (by intro operation; simp [groupOperationEvent]),
    powerCheckEnvelope_groupOperation_count, zero_add]
  simp [acceptanceEvents, groupOperationEvent, ResourcePool.ofList, ResourcePool.count]

/-- Quantum gates and quantum-oracle calls are absent from the classical
recovery-attempt allowance. -/
public theorem attemptEnvelope_count_nonclassical
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (event : Resource.Event (OrderExecution.model P))
    (outsideOperation : ∀ operation, event ≠ .classicalOperation operation)
    (outsideQuery : ∀ query, event ≠ .classicalQuery query) :
    ResourcePool.count event (attemptEnvelope P spec) = 0 := by
  have resetZero : ResourcePool.count event (ResourcePool.singleton (resetEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (outsideQuery .reset) 1
  have operationZero :
      ResourcePool.count event (ResourcePool.singleton (groupOperationEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (outsideQuery .groupOperation) 1
  have equalityZero :
      ResourcePool.count event (ResourcePool.singleton (equalityTestEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (outsideQuery .equalityTest) 1
  have acceptanceZero :
      ResourcePool.count event (ResourcePool.ofList (acceptanceEvents P)) = 0 := by
    simp [acceptanceEvents, ResourcePool.ofList, ResourcePool.count, outsideOperation]
  simp only [attemptEnvelope, ResourcePool.count_add,
    RawRecovery.Native.singleExposureEnvelope_count_nonclassical
      event outsideOperation, zero_add]
  simp only [powerCheckEnvelope, powerSiteEnvelope, ResourcePool.count_add,
    ResourcePool.count_scale, resetZero, operationZero, equalityZero,
    acceptanceZero, Nat.mul_zero, zero_add]

/-- An event-duration bound for one complete checked recovery attempt. -/
@[expose] public def attemptDepthLimit
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (duration : Resource.Event (OrderExecution.model P) → Nat) : Nat :=
  RawRecovery.Native.singleExposureDepthLimit spec duration +
    (duration (resetEvent P) +
      (OrderPreparation.width P *
          (duration (groupOperationEvent P) + duration (groupOperationEvent P)) +
        (duration (equalityTestEvent P) +
          ((acceptanceEvents P).map duration).sum)))

/-- Raw-recovery scratch is released before the continuation; hidden group
state contributes no caller-addressable storage coordinate. -/
public def attemptActiveSpace
    (additional : SpacePool .quantum) : SpacePool .quantum :=
  SpacePool.max
    (((RawRecovery.Native.preparationShapes (OrderPreparation.width P)).map
        SpacePool.ofShape).sum +
      RawRecovery.Native.singleExposureActiveSpace .quantum
        (OrderPreparation.width P))
    additional

variable
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : AttemptRefs ctx (OrderPreparation.width P))
    (body : CInputRef ctx (.unsignedWord (OrderPreparation.width P)) →
      CInputRef ctx .bit → Circuit (OrderExecution.model P) ctx ctx)

private theorem acceptanceSuffix_resident_le
    (path : (acceptanceSuffix P refs).Path) :
    (acceptanceSuffix P refs).peakResidentSpace path ≤ ctx.residentSpace := by
  unfold acceptanceSuffix at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    (le_of_eq (Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := OrderExecution.model P)
        (rawAcceptanceOp refs)) path.1))
    (le_of_eq (Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := OrderExecution.model P)
        (candidateAcceptanceOp refs)) path.2))

private theorem acceptanceSuffix_auxiliary_le
    (path : (acceptanceSuffix P refs).Path) :
    (acceptanceSuffix P refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  unfold acceptanceSuffix at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    (le_of_eq (Circuit.peakAuxiliarySpace_classical
      (BitWord.selectedApplication (execution := OrderExecution.model P)
        (rawAcceptanceOp refs)) path.1))
    (le_of_eq (Circuit.peakAuxiliarySpace_classical
      (BitWord.selectedApplication (execution := OrderExecution.model P)
        (candidateAcceptanceOp refs)) path.2))

public theorem attemptBody_pool_le (additional : ResourcePool (OrderExecution.model P))
    (bodyBound : ∀ candidate accepted path,
      (body candidate accepted).resourcePool path ≤ additional)
    (path : (attemptBody P spec input refs body).Path) :
    (attemptBody P spec input refs body).resourcePool path ≤
      attemptEnvelope P spec + additional := by
  change ResourcePool.ofList (_ ++ (_ ++ (_ ++ _))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append,
    ResourcePool.ofList_append, acceptanceSuffix_eventTrace]
  simpa only [Circuit.resourcePool, attemptEnvelope, add_assoc] using add_le_add
      (RawRecovery.Native.singleIntoCells_pool_le
        (model := OrderExecution.model P) spec input refs.inverseSuccess refs.candidate
          refs.reconstruction path.1)
      (add_le_add (powerCheck_pool_le P _ refs.powerEqualsTarget path.2.1)
        (add_le_add le_rfl (bodyBound _ _ path.2.2.2)))

public theorem attemptBody_depth_le
    (duration : Resource.Event (OrderExecution.model P) → Nat) (additional : Nat)
    (bodyBound : ∀ candidate accepted path,
      (body candidate accepted).depth duration path ≤ additional)
    (path : (attemptBody P spec input refs body).Path) :
    (attemptBody P spec input refs body).depth duration path ≤
      attemptDepthLimit P spec duration + additional := by
  change _ + (_ + (_ + _)) ≤ _
  have raw := RawRecovery.Native.singleIntoCells_depth_le
    (model := OrderExecution.model P) spec input refs.inverseSuccess refs.candidate
      refs.reconstruction duration path.1
  have checked := powerCheck_depth_le P _ refs.powerEqualsTarget duration path.2.1
  have accepted := le_of_eq (acceptanceSuffix_depth P refs duration path.2.2.1)
  have continued := bodyBound _ _ path.2.2.2
  exact (Nat.add_le_add raw
    (Nat.add_le_add checked (Nat.add_le_add accepted continued))).trans
      (le_of_eq (by simp only [attemptDepthLimit, Nat.add_assoc]))

/-- One attempt takes the maximum of released raw scratch and its continuation. -/
public theorem attemptBody_resident_le (additional : SpacePool .quantum)
    (bodyBound : ∀ candidate accepted path,
      (body candidate accepted).peakResidentSpace path ≤ additional + ctx.residentSpace)
    (path : (attemptBody P spec input refs body).Path) :
    (attemptBody P spec input refs body).peakResidentSpace path ≤
      attemptActiveSpace P additional + ctx.residentSpace := by
  unfold attemptBody at path ⊢
  rw [Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_seq]
  refine SpacePool.max_le ?_ (SpacePool.max_le ?_ (SpacePool.max_le ?_ ?_))
  · exact (RawRecovery.Native.singleIntoCells_resident_le
      (model := OrderExecution.model P) spec input refs.inverseSuccess refs.candidate
        refs.reconstruction path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (powerCheck_resident_le P _ refs.powerEqualsTarget path.2.1).trans
      (le_add_of_nonneg_left zero_le)
  · exact (acceptanceSuffix_resident_le P refs path.2.2.1).trans
      (le_add_of_nonneg_left zero_le)
  · exact (bodyBound _ _ path.2.2.2).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The same phase maximum bounds all auxiliary roles. -/
public theorem attemptBody_auxiliary_le (additional : SpacePool .quantum)
    (bodyBound : ∀ candidate accepted path,
      (body candidate accepted).peakAuxiliarySpace path ≤ additional + ctx.auxiliarySpace)
    (path : (attemptBody P spec input refs body).Path) :
    (attemptBody P spec input refs body).peakAuxiliarySpace path ≤
      attemptActiveSpace P additional + ctx.auxiliarySpace := by
  unfold attemptBody at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_seq]
  refine SpacePool.max_le ?_ (SpacePool.max_le ?_ (SpacePool.max_le ?_ ?_))
  · exact (RawRecovery.Native.singleIntoCells_auxiliary_le
      (model := OrderExecution.model P) spec input refs.inverseSuccess refs.candidate
        refs.reconstruction path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (powerCheck_auxiliary_le P _ refs.powerEqualsTarget path.2.1).trans
      (le_add_of_nonneg_left zero_le)
  · exact (acceptanceSuffix_auxiliary_le P refs path.2.2.1).trans
      (le_add_of_nonneg_left zero_le)
  · exact (bodyBound _ _ path.2.2.2).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- Attempt-cell allocation preserves the complete event allowance. -/
public theorem withAttempt_pool_le
    (outerBody : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → Transport ctx inner →
        Circuit (OrderExecution.model P) inner inner)
    (additional : ResourcePool (OrderExecution.model P))
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)))
      (accepted : CInputRef inner .bit) (transport : Transport ctx inner)
      (path : (outerBody candidate accepted transport).Path),
      (outerBody candidate accepted transport).resourcePool path ≤ additional)
    (path : (withAttempt P spec input outerBody).Path) :
    (withAttempt P spec input outerBody).resourcePool path ≤
      attemptEnvelope P spec + additional := by
  apply withCellsFrom_pool_le
  intro inner cells distinct transport separated selected
  exact attemptBody_pool_le P spec (transport.liftInput input) (attemptRefs cells) _ additional
    (fun candidate accepted path => bodyBound candidate accepted transport path) selected

/-- Attempt-cell allocation preserves the complete dependency allowance. -/
public theorem withAttempt_depth_le
    (outerBody : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → Transport ctx inner →
        Circuit (OrderExecution.model P) inner inner)
    (duration : Resource.Event (OrderExecution.model P) → Nat) (additional : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)))
      (accepted : CInputRef inner .bit) (transport : Transport ctx inner)
      (path : (outerBody candidate accepted transport).Path),
      (outerBody candidate accepted transport).depth duration path ≤ additional)
    (path : (withAttempt P spec input outerBody).Path) :
    (withAttempt P spec input outerBody).depth duration path ≤
      attemptDepthLimit P spec duration + additional := by
  apply withCellsFrom_depth_le
  intro inner cells distinct transport separated selected
  exact attemptBody_depth_le P spec (transport.liftInput input) (attemptRefs cells) _
    duration additional (fun candidate accepted path =>
      bodyBound candidate accepted transport path) selected

/-- Six attempt cells enclose one reused resident phase maximum. -/
public theorem withAttempt_resident_le
    (outerBody : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → Transport ctx inner →
        Circuit (OrderExecution.model P) inner inner)
    (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)))
      (accepted : CInputRef inner .bit) (transport : Transport ctx inner)
      (path : (outerBody candidate accepted transport).Path),
      (outerBody candidate accepted transport).peakResidentSpace path ≤
        additional + inner.residentSpace)
    (path : (withAttempt P spec input outerBody).Path) :
    (withAttempt P spec input outerBody).peakResidentSpace path ≤
      ((attemptShapes (OrderPreparation.width P)).map SpacePool.ofShape).sum +
        attemptActiveSpace P additional + ctx.residentSpace := by
  exact withCellsFrom_resident_le (model := OrderExecution.model P) (Transport.id ctx)
    (attemptShapes (OrderPreparation.width P))
    (fun cells _ transport _ =>
      attemptBody P spec (transport.liftInput input) (attemptRefs cells)
        (fun candidate accepted => outerBody candidate accepted transport))
    (attemptActiveSpace P additional) (by
      intro inner cells distinct transport separated selected
      exact attemptBody_resident_le P spec (transport.liftInput input) (attemptRefs cells) _
        additional (fun candidate accepted path =>
          bodyBound candidate accepted transport path) selected) path

/-- The same six cells enclose one reused auxiliary phase maximum. -/
public theorem withAttempt_auxiliary_le
    (outerBody : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → Transport ctx inner →
        Circuit (OrderExecution.model P) inner inner)
    (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)))
      (accepted : CInputRef inner .bit) (transport : Transport ctx inner)
      (path : (outerBody candidate accepted transport).Path),
      (outerBody candidate accepted transport).peakAuxiliarySpace path ≤
        additional + inner.auxiliarySpace)
    (path : (withAttempt P spec input outerBody).Path) :
    (withAttempt P spec input outerBody).peakAuxiliarySpace path ≤
      ((attemptShapes (OrderPreparation.width P)).map SpacePool.ofShape).sum +
        attemptActiveSpace P additional + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (model := OrderExecution.model P) (Transport.id ctx)
    (attemptShapes (OrderPreparation.width P))
    (fun cells _ transport _ =>
      attemptBody P spec (transport.liftInput input) (attemptRefs cells)
        (fun candidate accepted => outerBody candidate accepted transport))
    (attemptActiveSpace P additional) (by
      intro inner cells distinct transport separated selected
      exact attemptBody_auxiliary_le P spec (transport.liftInput input) (attemptRefs cells) _
        additional (fun candidate accepted path =>
          bodyBound candidate accepted transport path) selected) path

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
