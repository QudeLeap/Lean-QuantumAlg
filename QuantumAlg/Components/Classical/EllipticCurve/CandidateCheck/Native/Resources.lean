/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained
import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Space
import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native.Resources

/-!
# Actual resources of original candidate verification

The original scalar multiplication, complete point comparison and two Boolean
conjunctions retain their own native allowances in chronological order. Both
actual retained outputs coexist with every active verification scope. These
are derived pathwise upper bounds; the duration equation uses the same real
path and native event trace without a point or success assumption.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The four actual stages retain the scalar, comparator and two original AND allowances. -/
def verificationStageEnvelope (kind : ProblemKind) (spec : CurveSpec width)
    (scalarWidth : Nat) : Fin 4 → ResourcePool kind :=
  let conjunction := ResourcePool.ofList [.classicalOperation (.bit .and)]
  ![ScalarMul.Native.scalarEnvelope kind spec scalarWidth,
    PointEquality.coreEnvelope width, conjunction, conjunction]

/-- The original four stage allowances add without replacing any stage by a shared maximum. -/
def verificationEnvelope (kind : ProblemKind) (spec : CurveSpec width) (scalarWidth : Nat) :
    ResourcePool kind :=
  ∑ index, verificationStageEnvelope kind spec scalarWidth index

/-- Arbitrary native durations remain attached to each original chronological stage. -/
def verificationStageDepthLimit (spec : CurveSpec width) (scalarWidth : Nat)
    (duration : Resource.Event kind → Nat) : Fin 4 → Nat :=
  ![ScalarMul.Native.scalarDepthLimit spec scalarWidth duration,
    ((PointEquality.coreTrace width).map duration).sum,
    duration (.classicalOperation (.bit .and)), duration (.classicalOperation (.bit .and))]

/-- The original dependent four-stage execution adds all its native duration allowances. -/
def verificationDepthLimit (spec : CurveSpec width) (scalarWidth : Nat)
    (duration : Resource.Event kind → Nat) : Nat :=
  ∑ index, verificationStageDepthLimit spec scalarWidth duration index

/-- Scalar arithmetic and complete comparison have successive actual internal scopes. -/
def verificationScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (ScalarMul.Native.scalarScratchSpace kind width)
    (((PointEquality.Native.scratchShapes width).map SpacePool.ofShape).sum)

private theorem verificationStage_pool_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (index : Fin 4)
    (path : (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted index).Path) :
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted index).resourcePool path ≤
      verificationStageEnvelope kind spec scalarWidth index := by
  fin_cases index
  · exact ScalarMul.Native.scalarInto_pool_le spec _ _ _ path
  · exact (PointEquality.Native.compareInto_resourcePool _ _ _ path).le
  · exact le_rfl
  · exact le_rfl

/-- Every actual verification path keeps the four original stage resource allowances. -/
theorem verifyInto_pool_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (path : (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).Path) :
    (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).resourcePool path ≤ verificationEnvelope kind spec scalarWidth :=
  Circuit.forRange_pool_le_sum 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)
    (verificationStageEnvelope kind spec scalarWidth)
    (verificationStage_pool_le spec candidate base target inverseSuccess reconstruction
      scalarResult accepted) path

private theorem verificationStage_depth_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat) (index : Fin 4)
    (path : (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted index).Path) :
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted index).depth duration path ≤
      verificationStageDepthLimit spec scalarWidth duration index := by
  fin_cases index
  · exact ScalarMul.Native.scalarInto_depth_le spec _ _ _ duration path
  · exact (PointEquality.Native.compareInto_depth _ _ _ duration path).le
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- Every original dependency duration is retained by the actual four-stage verification. -/
theorem verifyInto_depth_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).Path) :
    (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).depth duration path ≤
      verificationDepthLimit spec scalarWidth duration :=
  Circuit.forRange_depth_le_sum 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)
    duration (verificationStageDepthLimit spec scalarWidth duration)
    (verificationStage_depth_le spec candidate base target inverseSuccess reconstruction
      scalarResult accepted duration) path

private theorem verificationStage_duration_eventTrace (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat) (index : Fin 4)
    (path : (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted index).Path) :
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted index).depth duration path =
      (((verificationStage spec candidate base target inverseSuccess reconstruction
        scalarResult accepted index).eventTrace path).map duration).sum := by
  fin_cases index
  · exact ScalarMul.Native.scalarInto_duration_eventTrace spec _ _ _ duration path
  · exact (PointEquality.Native.compareInto_depth _ _ _ duration path).trans
      (congrArg (fun events => (events.map duration).sum)
        (PointEquality.Native.compareInto_eventTrace _ _ _ path).symm)
  · exact (Nat.add_zero _).symm
  · exact (Nat.add_zero _).symm

/-- The same real path has exactly the sum of its own native event durations. -/
theorem verifyInto_duration_eventTrace (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).Path) :
    (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).depth duration path =
      (((verifyInto spec candidate base target inverseSuccess reconstruction
        scalarResult accepted).eventTrace path).map duration).sum :=
  Circuit.forRange_duration_eventTrace 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)
    duration (verificationStage_duration_eventTrace spec candidate base target inverseSuccess
      reconstruction scalarResult accepted duration) path

/-- Both actual retained allocations preserve the original native event allowance. -/
theorem retainedCircuit_pool_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (path : (retainedCircuit spec candidate base target inverseSuccess reconstruction).Path) :
    (retainedCircuit spec candidate base target inverseSuccess reconstruction).resourcePool path ≤
      verificationEnvelope kind spec scalarWidth :=
  verifyInto_pool_le spec _ _ _ _ _ _ _ path.2

/-- Both actual retained allocations add no native dependency event. -/
theorem retainedCircuit_depth_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (retainedCircuit spec candidate base target inverseSuccess reconstruction).Path) :
    (retainedCircuit spec candidate base target inverseSuccess reconstruction).depth duration path ≤
      verificationDepthLimit spec scalarWidth duration := by
  change 0 + _ ≤ _
  rw [zero_add]
  exact verifyInto_depth_le spec _ _ _ _ _ _ _ duration path.2

/-- Retention preserves the duration identity of the actual complete verification path. -/
theorem retainedCircuit_duration_eventTrace (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (retainedCircuit spec candidate base target inverseSuccess reconstruction).Path) :
    (retainedCircuit spec candidate base target inverseSuccess reconstruction).depth duration path =
      (((retainedCircuit spec candidate base target inverseSuccess reconstruction).eventTrace
        path).map duration).sum := by
  change 0 + _ = (List.map duration _).sum
  rw [zero_add]
  exact verifyInto_duration_eventTrace spec _ _ _ _ _ _ _ duration path.2

/-- Every real verification stage keeps the entire original resident context. -/
theorem verifyInto_resident_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (path : (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).Path) :
    (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).peakResidentSpace path ≤
      verificationScratchSpace kind width + ctx.residentSpace := by
  refine Circuit.forRange_resident_le 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted) (verificationScratchSpace kind width + ctx.residentSpace)
    le_add_self ?_ path
  intro index selected
  fin_cases index
  · exact (ScalarMul.Native.scalarInto_resident_le spec _ _ _ selected).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (PointEquality.Native.compareInto_resident _ _ _ selected).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  · exact (Circuit.peakResidentSpace_classical _ selected).le.trans le_add_self
  · exact (Circuit.peakResidentSpace_classical _ selected).le.trans le_add_self

private theorem retainOutputs_resident_le (ctx : RuntimeCtx kind) (width : Nat)
    (path : (retainOutputs ctx width).Path) :
    (retainOutputs ctx width).peakResidentSpace path ≤ (retainedCtx ctx width).residentSpace := by
  have first : ctx.residentSpace ≤ (acceptedCtx ctx).residentSpace := le_add_self
  have second : (acceptedCtx ctx).residentSpace ≤ (retainedCtx ctx width).residentSpace :=
    le_add_self
  change SpacePool.max ctx.residentSpace (SpacePool.max (acceptedCtx ctx).residentSpace
    (SpacePool.max (acceptedCtx ctx).residentSpace
      (SpacePool.max (retainedCtx ctx width).residentSpace 0))) ≤ _
  rw [SpacePool.max_zero]
  exact SpacePool.max_le (first.trans second)
    (SpacePool.max_le second (SpacePool.max_le second le_rfl))

/-- Both genuine retained outputs stay charged throughout the complete resident path. -/
theorem retainedCircuit_resident_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (path : (retainedCircuit spec candidate base target inverseSuccess reconstruction).Path) :
    (retainedCircuit spec candidate base target inverseSuccess reconstruction).peakResidentSpace
      path ≤
      verificationScratchSpace kind width + SpacePool.ofShape (PointShape width) +
        SpacePool.ofShape .bit + ctx.residentSpace := by
  let body := verifyInto spec (retainedInput width candidate) (retainedInput width base)
    (retainedInput width target) (retainedInput width inverseSuccess)
    (retainedInput width reconstruction) (retainedScalar ctx width) (retainedAccepted ctx width)
  refine (Circuit.peakResidentSpace_seq (retainOutputs ctx width) body path).le.trans ?_
  have bounded : SpacePool.max ((retainOutputs ctx width).peakResidentSpace path.1)
      (body.peakResidentSpace path.2) ≤
      verificationScratchSpace kind width + (retainedCtx ctx width).residentSpace :=
    SpacePool.max_le ((retainOutputs_resident_le ctx width path.1).trans le_add_self)
      (verifyInto_resident_le spec _ _ _ _ _ _ _ path.2)
  simpa only [retainedCtx, acceptedCtx, RuntimeCtx.residentSpace_addRetained, add_assoc]
    using bounded

/-- Every real verification stage keeps the entire original auxiliary context. -/
theorem verifyInto_auxiliary_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (path : (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).Path) :
    (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).peakAuxiliarySpace path ≤
      verificationScratchSpace kind width + ctx.auxiliarySpace := by
  refine Circuit.forRange_auxiliary_le 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted) (verificationScratchSpace kind width + ctx.auxiliarySpace)
    le_add_self ?_ path
  intro index selected
  fin_cases index
  · exact (ScalarMul.Native.scalarInto_auxiliary_le spec _ _ _ selected).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (PointEquality.Native.compareInto_auxiliary _ _ _ selected).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  · exact (Circuit.peakAuxiliarySpace_classical _ selected).le.trans le_add_self
  · exact (Circuit.peakAuxiliarySpace_classical _ selected).le.trans le_add_self

private theorem retainOutputs_auxiliary_le (ctx : RuntimeCtx kind) (width : Nat)
    (path : (retainOutputs ctx width).Path) :
    (retainOutputs ctx width).peakAuxiliarySpace path ≤ (retainedCtx ctx width).auxiliarySpace := by
  have first : ctx.auxiliarySpace ≤ (acceptedCtx ctx).auxiliarySpace := le_add_self
  have second : (acceptedCtx ctx).auxiliarySpace ≤ (retainedCtx ctx width).auxiliarySpace :=
    le_add_self
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max (acceptedCtx ctx).auxiliarySpace
    (SpacePool.max (acceptedCtx ctx).auxiliarySpace
      (SpacePool.max (retainedCtx ctx width).auxiliarySpace 0))) ≤ _
  rw [SpacePool.max_zero]
  exact SpacePool.max_le (first.trans second)
    (SpacePool.max_le second (SpacePool.max_le second le_rfl))

/-- Both genuine retained outputs stay charged throughout the complete auxiliary path. -/
theorem retainedCircuit_auxiliary_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (path : (retainedCircuit spec candidate base target inverseSuccess reconstruction).Path) :
    (retainedCircuit spec candidate base target inverseSuccess reconstruction).peakAuxiliarySpace
      path ≤
      verificationScratchSpace kind width + SpacePool.ofShape (PointShape width) +
        SpacePool.ofShape .bit + ctx.auxiliarySpace := by
  let body := verifyInto spec (retainedInput width candidate) (retainedInput width base)
    (retainedInput width target) (retainedInput width inverseSuccess)
    (retainedInput width reconstruction) (retainedScalar ctx width) (retainedAccepted ctx width)
  refine (Circuit.peakAuxiliarySpace_seq (retainOutputs ctx width) body path).le.trans ?_
  have bounded : SpacePool.max ((retainOutputs ctx width).peakAuxiliarySpace path.1)
      (body.peakAuxiliarySpace path.2) ≤
      verificationScratchSpace kind width + (retainedCtx ctx width).auxiliarySpace :=
    SpacePool.max_le ((retainOutputs_auxiliary_le ctx width path.1).trans le_add_self)
      (verifyInto_auxiliary_le spec _ _ _ _ _ _ _ path.2)
  simpa only [retainedCtx, acceptedCtx, RuntimeCtx.auxiliarySpace_addRetained, add_assoc]
    using bounded

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
