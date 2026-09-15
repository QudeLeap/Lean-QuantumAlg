/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Dispatch.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Infinity.Resources

/-!
# Original resources of actual complete point addition

The original classifier precedes exactly one original arm. Events and serial
durations add its allowance to the original nested arm maximum. All classifier
cells stay live with the selected arm's original workspace. Every bound refers
to the same actual native circuit and its complete selected paths.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def caseMaximum {α : Type} (combine : α → α → α) (values : Case → α) : α :=
  combine (values .leftInfinity) (combine (values .rightInfinity)
    (combine (combine (combine (values .vertical) (values .doubling)) (values .vertical))
      (values .generic)))

private theorem case_le_caseMaximum {α : Type} [Preorder α]
    (combine : α → α → α) (belowLeft : ∀ left right, left ≤ combine left right)
    (belowRight : ∀ left right, right ≤ combine left right) (values : Case → α)
    (selected : Case) : values selected ≤ caseMaximum combine values := by
  unfold caseMaximum
  cases selected
  · exact belowLeft _ _
  · exact (belowLeft _ _).trans (belowRight _ _)
  · exact (belowRight _ _).trans
      ((belowLeft _ _).trans ((belowRight _ _).trans (belowRight _ _)))
  · exact (belowRight _ _).trans
      ((belowLeft _ _).trans ((belowLeft _ _).trans
        ((belowRight _ _).trans (belowRight _ _))))
  · exact (belowRight _ _).trans ((belowRight _ _).trans (belowRight _ _))

/-- Original independent native allowance of each actual complete-addition arm. -/
def additionArmEnvelope (kind : ProblemKind) (spec : CurveSpec width) : Case → ResourcePool kind
  | .leftInfinity | .rightInfinity =>
      ResourcePool.ofList [.classicalOperation (.nominalEncoding (.packEllipticCurvePoint width))]
  | .vertical => ResourcePool.ofList (infinityTrace width)
  | .doubling => doublingEnvelope kind spec
  | .generic => genericEnvelope kind spec.field

/-- Original alternatives retain the native coordinate maximum of the actual dispatch tree. -/
def additionBranchEnvelope (kind : ProblemKind) (spec : CurveSpec width) : ResourcePool kind :=
  caseMaximum ResourcePool.max (additionArmEnvelope kind spec)

/-- Original classifier events precede the actual complete arm allowance. -/
def additionEnvelope (kind : ProblemKind) (spec : CurveSpec width) : ResourcePool kind :=
  ResourcePool.ofList (classifierTrace width) + additionBranchEnvelope kind spec

/-- Original independent serial duration allowance of each actual arm. -/
def additionArmDepthLimit (spec : CurveSpec width) (duration : Resource.Event kind → Nat) :
    Case → Nat
  | .leftInfinity | .rightInfinity =>
      duration (.classicalOperation (.nominalEncoding (.packEllipticCurvePoint width)))
  | .vertical => ((infinityTrace width).map duration).sum
  | .doubling => doublingDepthLimit spec duration
  | .generic => genericDepthLimit spec.field duration

/-- Original classifier durations precede the original conditional arm maximum. -/
def additionDepthLimit (spec : CurveSpec width) (duration : Resource.Event kind → Nat) : Nat :=
  ((classifierTrace width).map duration).sum +
    caseMaximum Nat.max (additionArmDepthLimit spec duration)

/-- Each actual arm owns its complete original lexical workspace. -/
def additionArmSpace (kind : ProblemKind) (width : Nat) : Case → SpacePool kind
  | .leftInfinity | .rightInfinity => 0
  | .vertical => ((infinityShapes width).map SpacePool.ofShape).sum
  | .doubling => ((doublingShapes width).map SpacePool.ofShape).sum +
      doublingActiveSpace kind width
  | .generic => ((genericShapes width).map SpacePool.ofShape).sum + genericActiveSpace kind width

/-- Only the selected original arm's real lexical workspace is active. -/
def additionActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  caseMaximum SpacePool.max (additionArmSpace kind width)

/-- Both full snapshots and all classifier cells coexist with the actual selected arm. -/
def additionScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((classifierShapes width).map SpacePool.ofShape).sum + additionActiveSpace kind width


private theorem additionArm_pool_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (selected : Case) (path : (additionArm spec classifier output selected).Path) :
    (additionArm spec classifier output selected).resourcePool path ≤
      additionArmEnvelope kind spec selected := by
  cases selected
  all_goals first
    | exact le_rfl
    | exact (infinityInto_resourcePool _ path).le
    | exact doublingInto_pool_le _ _ _ path
    | exact genericInto_pool_le _ _ _ _ path

private theorem additionDispatch_pool_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (path : (dispatch classifier (additionArm spec classifier output)).Path) :
    (dispatch classifier (additionArm spec classifier output)).resourcePool path ≤
      additionBranchEnvelope kind spec := by
  obtain ⟨selected, armPath, trace, _, _⟩ := dispatch_selectedTrace classifier
    (additionArm spec classifier output) path
  exact (congrArg ResourcePool.ofList trace).le.trans
    ((additionArm_pool_le spec classifier output selected armPath).trans
      (case_le_caseMaximum ResourcePool.max ResourcePool.le_max_left ResourcePool.le_max_right
        (additionArmEnvelope kind spec) selected))

private theorem additionArm_depth_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (selected : Case) (path : (additionArm spec classifier output selected).Path) :
    (additionArm spec classifier output selected).depth duration path ≤
      additionArmDepthLimit spec duration selected := by
  cases selected
  all_goals first
    | exact (repackRawInto_depth _ _ duration path).le
    | exact (infinityInto_depth _ duration path).le
    | exact doublingInto_depth_le _ _ _ duration path
    | exact genericInto_depth_le _ _ _ _ duration path

private theorem additionDispatch_depth_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (dispatch classifier (additionArm spec classifier output)).Path) :
    (dispatch classifier (additionArm spec classifier output)).depth duration path ≤
      caseMaximum Nat.max (additionArmDepthLimit spec duration) := by
  obtain ⟨selected, armPath, _, dependencies, _⟩ := dispatch_selectedTrace classifier
    (additionArm spec classifier output) path
  exact (congrArg (DepthExpr.depthEval duration) dependencies).le.trans
    ((additionArm_depth_le spec classifier output duration selected armPath).trans
      (case_le_caseMaximum Nat.max Nat.le_max_left Nat.le_max_right
        (additionArmDepthLimit spec duration) selected))

private theorem additionArm_duration_eventTrace (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (selected : Case) (path : (additionArm spec classifier output selected).Path) :
    (additionArm spec classifier output selected).depth duration path =
      (((additionArm spec classifier output selected).eventTrace path).map duration).sum := by
  cases selected
  · exact (Nat.add_zero _).symm
  · exact (Nat.add_zero _).symm
  · exact (infinityInto_depth output duration path).trans
      (congrArg (fun events => (events.map duration).sum)
        (infinityInto_eventTrace output path).symm)
  · exact doublingInto_duration_eventTrace spec (classifierRead classifier.leftRaw)
      output duration path
  · exact genericInto_duration_eventTrace spec.field (classifierRead classifier.leftRaw)
      (classifierRead classifier.rightRaw) output duration path

private theorem additionDispatch_duration_eventTrace (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (dispatch classifier (additionArm spec classifier output)).Path) :
    (dispatch classifier (additionArm spec classifier output)).depth duration path =
      (((dispatch classifier (additionArm spec classifier output)).eventTrace path).map
        duration).sum := by
  obtain ⟨selected, armPath, trace, dependencies, _⟩ := dispatch_selectedTrace classifier
    (additionArm spec classifier output) path
  exact (congrArg (DepthExpr.depthEval duration) dependencies).trans
    ((additionArm_duration_eventTrace spec classifier output duration selected armPath).trans
      (congrArg (fun events => (events.map duration).sum) trace.symm))

/-- The actual complete path retains the original classifier and selected-arm accounting. -/
theorem addInto_pool_le (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (addInto spec left right output).Path) :
    (addInto spec left right output).resourcePool path ≤ additionEnvelope kind spec := by
  apply withCellsFrom_property (Transport.id ctx) (classifierShapes width)
    (fun cells _ transport _ =>
      .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells))
        (dispatch (classifierOfCells cells)
          (additionArm spec (classifierOfCells cells) (transport.liftWrite output))))
    (fun _ code => ∀ selected, code.resourcePool selected ≤ additionEnvelope kind spec)
    (fun _ _ _ _ _ available => available) _ path
  intro inner cells _ transport _ selected
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (classifierBody_resourcePool _ _ _ selected.1).le
    (additionDispatch_pool_le _ _ _ selected.2)

/-- The actual complete path retains the original classifier and selected-arm accounting. -/
theorem addInto_depth_le (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (addInto spec left right output).Path) :
    (addInto spec left right output).depth duration path ≤ additionDepthLimit spec duration := by
  apply withCellsFrom_property (Transport.id ctx) (classifierShapes width)
    (fun cells _ transport _ =>
      .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells))
        (dispatch (classifierOfCells cells)
          (additionArm spec (classifierOfCells cells) (transport.liftWrite output))))
    (fun _ code => ∀ selected, code.depth duration selected ≤ additionDepthLimit spec duration)
    (fun _ _ _ _ _ available => available) _ path
  intro inner cells _ transport _ selected
  exact Nat.add_le_add (classifierBody_depth _ _ _ duration selected.1).le
    (additionDispatch_depth_le _ _ _ duration selected.2)

/-- The actual complete path retains the original classifier and selected-arm accounting. -/
theorem addInto_duration_eventTrace (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (addInto spec left right output).Path) :
    (addInto spec left right output).depth duration path =
      (((addInto spec left right output).eventTrace path).map duration).sum := by
  apply withCellsFrom_property (Transport.id ctx) (classifierShapes width)
    (fun cells _ transport _ =>
      .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells))
        (dispatch (classifierOfCells cells)
          (additionArm spec (classifierOfCells cells) (transport.liftWrite output))))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available) _ path
  intro inner cells _ transport _ selected
  have classifiedDepth :=
    (classifierBody_depth (transport.liftInput left) (transport.liftInput right)
    (classifierOfCells cells) duration selected.1).trans
      (congrArg (fun events => (events.map duration).sum)
        (classifierBody_eventTrace (transport.liftInput left) (transport.liftInput right)
          (classifierOfCells cells) selected.1).symm)
  change _ + _ = (List.map duration
    ((classifierBody (transport.liftInput left) (transport.liftInput right)
      (classifierOfCells cells)).eventTrace selected.1 ++
      (dispatch (classifierOfCells cells)
        (additionArm spec (classifierOfCells cells) (transport.liftWrite output))).eventTrace
          selected.2)).sum
  rw [List.map_append, List.sum_append]
  exact congrArg₂ Nat.add classifiedDepth
    (additionDispatch_duration_eventTrace _ _ _ duration selected.2)

private theorem additionArm_resident_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (selected : Case) (path : (additionArm spec classifier output selected).Path) :
    (additionArm spec classifier output selected).peakResidentSpace path ≤
      additionArmSpace kind width selected + ctx.residentSpace := by
  cases selected
  all_goals first
    | exact (repackRawInto_resident _ _ path).le.trans_eq (zero_add _).symm
    | exact infinityInto_resident _ path
    | exact doublingInto_resident_le _ _ _ path
    | exact genericInto_resident_le _ _ _ _ path

private theorem additionDispatch_resident_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (path : (dispatch classifier (additionArm spec classifier output)).Path) :
    (dispatch classifier (additionArm spec classifier output)).peakResidentSpace path ≤
      additionActiveSpace kind width + ctx.residentSpace := by
  obtain ⟨selected, armPath, _, _, contexts⟩ := dispatch_selectedTrace classifier
    (additionArm spec classifier output) path
  exact (congrArg (Circuit.peak RuntimeCtx.residentSpace) contexts).le.trans
    ((additionArm_resident_le spec classifier output selected armPath).trans
      (add_le_add (case_le_caseMaximum SpacePool.max SpacePool.le_max_left SpacePool.le_max_right
        (additionArmSpace kind width) selected) le_rfl))

/-- All original classifier cells coexist with the largest actual complete arm scope. -/
theorem addInto_resident_le (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (addInto spec left right output).Path) :
    (addInto spec left right output).peakResidentSpace path ≤
      additionScratchSpace kind width + ctx.residentSpace :=
  withClassification_resident left right
    (fun classifier transport =>
      dispatch classifier (additionArm spec classifier (transport.liftWrite output)))
    (additionActiveSpace kind width)
    (fun classifier transport selected =>
      additionDispatch_resident_le spec classifier (transport.liftWrite output) selected) path

private theorem additionArm_auxiliary_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (selected : Case) (path : (additionArm spec classifier output selected).Path) :
    (additionArm spec classifier output selected).peakAuxiliarySpace path ≤
      additionArmSpace kind width selected + ctx.auxiliarySpace := by
  cases selected
  all_goals first
    | exact (repackRawInto_auxiliary _ _ path).le.trans_eq (zero_add _).symm
    | exact infinityInto_auxiliary _ path
    | exact doublingInto_auxiliary_le _ _ _ path
    | exact genericInto_auxiliary_le _ _ _ _ path

private theorem additionDispatch_auxiliary_le (spec : CurveSpec width)
    (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width))
    (path : (dispatch classifier (additionArm spec classifier output)).Path) :
    (dispatch classifier (additionArm spec classifier output)).peakAuxiliarySpace path ≤
      additionActiveSpace kind width + ctx.auxiliarySpace := by
  obtain ⟨selected, armPath, _, _, contexts⟩ := dispatch_selectedTrace classifier
    (additionArm spec classifier output) path
  exact (congrArg (Circuit.peak RuntimeCtx.auxiliarySpace) contexts).le.trans
    ((additionArm_auxiliary_le spec classifier output selected armPath).trans
      (add_le_add (case_le_caseMaximum SpacePool.max SpacePool.le_max_left SpacePool.le_max_right
        (additionArmSpace kind width) selected) le_rfl))

/-- All original classifier cells coexist with the largest actual complete arm scope. -/
theorem addInto_auxiliary_le (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (addInto spec left right output).Path) :
    (addInto spec left right output).peakAuxiliarySpace path ≤
      additionScratchSpace kind width + ctx.auxiliarySpace :=
  withClassification_auxiliary left right
    (fun classifier transport =>
      dispatch classifier (additionArm spec classifier (transport.liftWrite output)))
    (additionActiveSpace kind width)
    (fun classifier transport selected =>
      additionDispatch_auxiliary_le spec classifier (transport.liftWrite output) selected) path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
