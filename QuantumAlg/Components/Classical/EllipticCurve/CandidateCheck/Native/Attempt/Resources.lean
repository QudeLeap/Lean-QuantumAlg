/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Placement.Resources

/-!
# Actual original six-stage attempt resources

The raw three-cell recovery, four-stage candidate verification and original
first-accepted selector execute serially in one caller context. Their native
allowances add; their separate lexical scopes contribute a maximum. Every
persistent caller destination remains charged once, and no retained output
allocation is inserted into the repeated attempt.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open FiniteCyclicDLP.RawRecovery.Native

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Independent allowances retain raw recovery, actual verification and the original selector. -/
def attemptEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth) : ResourcePool model :=
  singleExposureEnvelope model modulus + verificationEnvelope model curve scalarWidth +
    FirstAccepted.nativeEnvelope model scalarWidth

/-- Arbitrary native durations retain the actual three serial circuit groups. -/
def attemptDepthLimit {model : ExecutionModel} [BitWord.Selected model]
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (duration : Resource.Event model → Nat) : Nat :=
  singleExposureDepthLimit modulus duration + verificationDepthLimit curve scalarWidth duration +
    ((FirstAccepted.decisionEvents model ++ FirstAccepted.copyEvents model scalarWidth).map
      duration).sum

/-- Only successive lexical scratch scopes contribute a maximum beside the caller context. -/
def attemptScratchSpace (kind : ProblemKind) (width scalarWidth : Nat) : SpacePool kind :=
  SpacePool.max
    (SpacePool.max (((preparationShapes scalarWidth).map SpacePool.ofShape).sum +
      singleExposureActiveSpace kind scalarWidth) (verificationScratchSpace kind width))
    (FirstAccepted.selectionScratchSpace kind)

variable (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))

/-- The actual attempt concatenates the same recorded raw, verification and selection traces. -/
lemma attemptInto_eventTrace
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).eventTrace path =
      ((singleIntoCells modulus sample inverseSuccess candidate reconstruction).eventTrace
        path.1.1 ++
        (verifyInto curve (.storage candidate.toCStorageRef) base target
          (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
          scalarResult targetAccepted).eventTrace path.1.2) ++
        (FirstAccepted.withSelection
          ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩
          accepted selected).eventTrace path.2 := rfl

/-- The same actual native pool decomposes into the three serial circuit groups. -/
lemma attemptInto_resourcePool
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).resourcePool path =
      (singleIntoCells modulus sample inverseSuccess candidate reconstruction).resourcePool
        path.1.1 +
        (verifyInto curve (.storage candidate.toCStorageRef) base target
          (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
          scalarResult targetAccepted).resourcePool path.1.2 +
        (FirstAccepted.withSelection
          ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩
          accepted selected).resourcePool path.2 := by
  rw [Circuit.resourcePool, attemptInto_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append]
  rfl

/-- Every actual path retains all original native operation allowances in their serial sum. -/
lemma attemptInto_pool_le
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).resourcePool path ≤
        attemptEnvelope model curve modulus := by
  rw [attemptInto_resourcePool]
  exact add_le_add
    (add_le_add (singleIntoCells_pool_le modulus sample inverseSuccess candidate reconstruction
      path.1.1) (verifyInto_pool_le curve _ base target _ _ scalarResult targetAccepted path.1.2))
    (FirstAccepted.withSelection_pool_le _ accepted selected path.2)

/-- Actual dependency depth is the serial sum on exactly the same three recorded paths. -/
lemma attemptInto_depth (duration : Resource.Event model → Nat)
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).depth duration path =
      (singleIntoCells modulus sample inverseSuccess candidate reconstruction).depth duration
        path.1.1 +
        (verifyInto curve (.storage candidate.toCStorageRef) base target
          (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
          scalarResult targetAccepted).depth duration path.1.2 +
        (FirstAccepted.withSelection
          ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩
          accepted selected).depth duration path.2 := rfl

/-- Arbitrary native duration allowances retain the original six-stage dependency order. -/
lemma attemptInto_depth_le (duration : Resource.Event model → Nat)
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).depth duration path ≤
        attemptDepthLimit curve modulus duration := by
  rw [attemptInto_depth]
  exact Nat.add_le_add
    (Nat.add_le_add (singleIntoCells_depth_le modulus sample inverseSuccess candidate reconstruction
      duration path.1.1)
      (verifyInto_depth_le curve _ base target _ _ scalarResult targetAccepted duration path.1.2))
    (FirstAccepted.withSelection_depth_le _ accepted selected duration path.2)

/-- The resident bound takes the maximum of three successive scratch scopes beside the caller. -/
lemma attemptInto_resident_le
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).peakResidentSpace path ≤
        attemptScratchSpace model.kind width scalarWidth + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact (singleIntoCells_resident_le modulus sample inverseSuccess candidate reconstruction
        path.1.1).trans
        (add_le_add ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_left _ _)) le_rfl)
    · exact (verifyInto_resident_le curve _ base target _ _ scalarResult targetAccepted
        path.1.2).trans
        (add_le_add ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_left _ _)) le_rfl)
  · exact (FirstAccepted.withSelection_resident _ accepted selected path.2).le.trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The auxiliary bound charges the same actual scope maximum and existing caller workspace. -/
lemma attemptInto_auxiliary_le
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).peakAuxiliarySpace path ≤
        attemptScratchSpace model.kind width scalarWidth + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact (singleIntoCells_auxiliary_le modulus sample inverseSuccess candidate reconstruction
        path.1.1).trans
        (add_le_add ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_left _ _)) le_rfl)
    · exact (verifyInto_auxiliary_le curve _ base target _ _ scalarResult targetAccepted
        path.1.2).trans
        (add_le_add ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_left _ _)) le_rfl)
  · exact (FirstAccepted.withSelection_auxiliary _ accepted selected path.2).le.trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
