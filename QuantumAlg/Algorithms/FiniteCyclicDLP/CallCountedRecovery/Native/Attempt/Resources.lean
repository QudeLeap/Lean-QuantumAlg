/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Power.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources

/-!
# Actual single-attempt events, duration and space

Raw preparation, checked inversion and all three copies retain their existing
independent allowance. Every attempt then performs the original declared-power
scan and all three acceptance operations. The six attempt cells remain live
through both phases; the additional accumulator is allocated only after raw
recovery workspaces end and stays live through the caller continuation.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- The original word comparison and both real flag conjunctions. -/
def acceptanceEvents (width : Nat) : List (Resource.Event .quantum) :=
  [.classicalOperation (.wordBinary .equal width), .classicalOperation (.bit .and),
    .classicalOperation (.bit .and)]

/-- Every actual suffix path executes precisely the original three test instructions. -/
theorem acceptanceSuffix_eventTrace (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (path : (acceptanceSuffix powered target refs).Path) :
    (acceptanceSuffix powered target refs).eventTrace path = acceptanceEvents width := rfl

/-- Arbitrary durations charge the same literal operations in their real serial order. -/
theorem acceptanceSuffix_depth (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (duration : Resource.Event .quantum → Nat)
    (path : (acceptanceSuffix powered target refs).Path) :
    (acceptanceSuffix powered target refs).depth duration path =
      ((acceptanceEvents width).map duration).sum := rfl

private theorem acceptance_visits (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (path : (acceptanceSuffix powered target refs).Path) :
    (acceptanceSuffix powered target refs).visitedContexts path = [ctx, ctx, ctx] := rfl

private theorem acceptance_resident (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (path : (acceptanceSuffix powered target refs).Path) :
    (acceptanceSuffix powered target refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited member
  rw [acceptance_visits] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst visited
  exact le_rfl

private theorem acceptance_auxiliary (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (path : (acceptanceSuffix powered target refs).Path) :
    (acceptanceSuffix powered target refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited member
  rw [acceptance_visits] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst visited
  exact le_rfl

/-- Independent original raw allowance, both possible declared calls, and all three tests. -/
def attemptEnvelope (P : Parameters G) : ResourcePool .quantum :=
  RawRecovery.Native.singleExposureEnvelope .quantum P.spec +
    (ResourcePool.scale (P.width - 1) (powerSiteEnvelope P.access) +
      ResourcePool.ofList (acceptanceEvents P.width))

/-- Original raw dependencies precede the full power scan and the same literal tests. -/
def attemptDepthLimit (P : Parameters G) (duration : Resource.Event .quantum → Nat) : Nat :=
  RawRecovery.Native.singleExposureDepthLimit P.spec duration +
    ((P.width - 1) * (duration (.classicalSubroutine P.access.squareLabel) +
      duration (.classicalSubroutine P.access.multiplyLabel)) +
        ((acceptanceEvents P.width).map duration).sum)

/-- Raw scratch is released before the accumulator and continuation become live. -/
def attemptActiveSpace (P : Parameters G) (additional : SpacePool .quantum) : SpacePool .quantum :=
  SpacePool.max
    (((RawRecovery.Native.preparationShapes P.width).map SpacePool.ofShape).sum +
      RawRecovery.Native.singleExposureActiveSpace .quantum P.width)
    (SpacePool.ofShape (.unsignedWord P.width) + additional)

variable (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : AttemptRefs ctx P.width)
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport ctx inner → Circuit inner inner)

/-- All original operations precede the real continuation on the same actual attempt path. -/
theorem attemptBody_pool_le (additional : ResourcePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).resourcePool path ≤ additional)
    (path : (attemptBody P input target refs body).Path) :
    (attemptBody P input target refs body).resourcePool path ≤ attemptEnvelope P + additional := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  have powered := withPowerAccumulator_pool_le P.access P.generator
    (.storage refs.candidate.toCStorageRef) _
    (ResourcePool.ofList (acceptanceEvents P.width) + additional) (by
      intro inner powered transport selected
      change ResourcePool.ofList (_ ++ _) ≤ _
      rw [ResourcePool.ofList_append, acceptanceSuffix_eventTrace]
      exact add_le_add le_rfl (bodyBound _ _ _ selected.2)) path.2
  exact (add_le_add (RawRecovery.Native.singleIntoCells_pool_le P.spec input
    refs.inverseSuccess refs.candidate refs.reconstruction path.1) powered).trans
      (le_of_eq (by simp only [attemptEnvelope, add_assoc]))

/-- Arbitrary durations retain the existing raw bound and the subsequent serial dependencies. -/
theorem attemptBody_depth_le (duration : Resource.Event .quantum → Nat) (additional : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).depth duration path ≤ additional)
    (path : (attemptBody P input target refs body).Path) :
    (attemptBody P input target refs body).depth duration path ≤
      attemptDepthLimit P duration + additional := by
  change _ + _ ≤ _
  have powered := withPowerAccumulator_depth_le P.access P.generator
    (.storage refs.candidate.toCStorageRef) _ duration
    (((acceptanceEvents P.width).map duration).sum + additional) (by
      intro inner powered transport selected
      change _ + _ ≤ _
      exact Nat.add_le_add (le_of_eq (acceptanceSuffix_depth _ _ _ duration selected.1))
        (bodyBound _ _ _ selected.2)) path.2
  exact (Nat.add_le_add (RawRecovery.Native.singleIntoCells_depth_le P.spec input
    refs.inverseSuccess refs.candidate refs.reconstruction duration path.1) powered).trans
      (le_of_eq (by simp only [attemptDepthLimit, Nat.add_assoc]))

/-- The actual resident maximum keeps raw scratch and the later accumulator in distinct phases. -/
theorem attemptBody_resident_le (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).peakResidentSpace path ≤ additional + inner.residentSpace)
    (path : (attemptBody P input target refs body).Path) :
    (attemptBody P input target refs body).peakResidentSpace path ≤
      attemptActiveSpace P additional + ctx.residentSpace := by
  dsimp only [attemptBody] at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · exact (RawRecovery.Native.singleIntoCells_resident_le P.spec input
      refs.inverseSuccess refs.candidate refs.reconstruction path.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · have powered := withPowerAccumulator_resident_le P.access P.generator
      (.storage refs.candidate.toCStorageRef) _ additional (by
        intro inner powered transport selected
        rw [Circuit.peakResidentSpace_seq]
        exact SpacePool.max_le
          ((acceptance_resident _ _ _ selected.1).trans (le_add_of_nonneg_left zero_le))
          (bodyBound _ _ _ selected.2)) path.2
    exact powered.trans (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The actual auxiliary maximum keeps raw scratch and the later accumulator in distinct phases. -/
theorem attemptBody_auxiliary_le (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).peakAuxiliarySpace path ≤
        additional + inner.auxiliarySpace)
    (path : (attemptBody P input target refs body).Path) :
    (attemptBody P input target refs body).peakAuxiliarySpace path ≤
      attemptActiveSpace P additional + ctx.auxiliarySpace := by
  dsimp only [attemptBody] at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · exact (RawRecovery.Native.singleIntoCells_auxiliary_le P.spec input
      refs.inverseSuccess refs.candidate refs.reconstruction path.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · have powered := withPowerAccumulator_auxiliary_le P.access P.generator
      (.storage refs.candidate.toCStorageRef) _ additional (by
        intro inner powered transport selected
        rw [Circuit.peakAuxiliarySpace_seq]
        exact SpacePool.max_le
          ((acceptance_auxiliary _ _ _ selected.1).trans (le_add_of_nonneg_left zero_le))
          (bodyBound _ _ _ selected.2)) path.2
    exact powered.trans (add_le_add (SpacePool.le_max_right _ _) le_rfl)


/-- The original six actual allocations preserve the full pool bound and caller context. -/
theorem withAttempt_pool_le (additional : ResourcePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).resourcePool path ≤ additional)
    (path : (withAttempt P input target body).Path) :
    (withAttempt P input target body).resourcePool path ≤ attemptEnvelope P + additional := by
  apply withCellsFrom_pool_le
  intro inner cells distinct transport separated selected
  exact attemptBody_pool_le P (transport.liftInput input) (transport.liftInput target)
    (attemptRefs cells) _ additional
    (fun candidate accepted innerTransport =>
      bodyBound candidate accepted (transport.compose innerTransport)) selected

/-- The original six actual allocations preserve the full depth bound and caller context. -/
theorem withAttempt_depth_le (duration : Resource.Event .quantum → Nat) (additional : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).depth duration path ≤ additional)
    (path : (withAttempt P input target body).Path) :
    (withAttempt P input target body).depth duration path ≤
      attemptDepthLimit P duration + additional := by
  apply withCellsFrom_depth_le
  intro inner cells distinct transport separated selected
  exact attemptBody_depth_le P (transport.liftInput input) (transport.liftInput target)
    (attemptRefs cells) _ duration additional
    (fun candidate accepted innerTransport =>
      bodyBound candidate accepted (transport.compose innerTransport)) selected

/-- The original six actual allocations preserve the full resident bound and caller context. -/
theorem withAttempt_resident_le (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).peakResidentSpace path ≤ additional + inner.residentSpace)
    (path : (withAttempt P input target body).Path) :
    (withAttempt P input target body).peakResidentSpace path ≤
      ((attemptShapes P.width).map SpacePool.ofShape).sum +
        attemptActiveSpace P additional + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (attemptShapes P.width)
    (fun cells _ transport _ =>
      attemptBody P (transport.liftInput input) (transport.liftInput target) (attemptRefs cells)
        (fun candidate accepted innerTransport =>
          body candidate accepted (transport.compose innerTransport)))
    (attemptActiveSpace P additional) (by
      intro inner cells distinct transport separated selected
      exact attemptBody_resident_le P (transport.liftInput input) (transport.liftInput target)
        (attemptRefs cells) _ additional
        (fun candidate accepted innerTransport =>
          bodyBound candidate accepted (transport.compose innerTransport)) selected) path

/-- The original six actual allocations preserve the full auxiliary bound and caller context. -/
theorem withAttempt_auxiliary_le (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord P.width)) (accepted : CInputRef inner .bit)
      (transport : Transport ctx inner) (path : (body candidate accepted transport).Path),
      (body candidate accepted transport).peakAuxiliarySpace path ≤
        additional + inner.auxiliarySpace)
    (path : (withAttempt P input target body).Path) :
    (withAttempt P input target body).peakAuxiliarySpace path ≤
      ((attemptShapes P.width).map SpacePool.ofShape).sum +
        attemptActiveSpace P additional + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (attemptShapes P.width)
    (fun cells _ transport _ =>
      attemptBody P (transport.liftInput input) (transport.liftInput target) (attemptRefs cells)
        (fun candidate accepted innerTransport =>
          body candidate accepted (transport.compose innerTransport)))
    (attemptActiveSpace P additional) (by
      intro inner cells distinct transport separated selected
      exact attemptBody_auxiliary_le P (transport.liftInput input) (transport.liftInput target)
        (attemptRefs cells) _ additional
        (fun candidate accepted innerTransport =>
          bodyBound candidate accepted (transport.compose innerTransport)) selected) path

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
