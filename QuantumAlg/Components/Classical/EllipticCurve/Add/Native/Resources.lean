/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual complete-addition classifier resources

Only the original two nominal adapters and three unsigned comparisons occur
before dispatch. All six actual classifier cells, including the zero word,
remain live through the chosen continuation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original ordered operations that establish complete affine branch predicates. -/
def classifierTrace (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.unpackEllipticCurvePoint width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.unpackEllipticCurvePoint width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width))]

/-- Every actual classifier path emits exactly the original five operations. -/
theorem classifierBody_eventTrace (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width)
    (path : (classifierBody (model := model) left right classifier).Path) :
    (classifierBody (model := model) left right classifier).eventTrace path =
      classifierTrace model width := by
  simp [classifierBody, Circuit.forRange, classifierStage, Circuit.eventTrace,
    BitWord.bitWord_instruction_eventTrace, classifierUnpackLeft, classifierUnpackRight,
    classifierEqualX, classifierEqualY, classifierZeroY, classifierTrace,
    ClassicalOp.label]

/-- Exact event multiplicities are derived from that same actual classifier trace. -/
theorem classifierBody_resourcePool (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width)
    (path : (classifierBody (model := model) left right classifier).Path) :
    (classifierBody (model := model) left right classifier).resourcePool path =
      ResourcePool.ofList (classifierTrace model width) :=
  congrArg ResourcePool.ofList (classifierBody_eventTrace left right classifier path)

/-- The actual classifier is serial in exactly the original five native event durations. -/
theorem classifierBody_depth (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (duration : Resource.Event model → Nat)
    (path : (classifierBody (model := model) left right classifier).Path) :
    (classifierBody (model := model) left right classifier).depth duration path =
      ((classifierTrace model width).map duration).sum := by
  rw [← classifierBody_eventTrace left right classifier path]
  apply Circuit.forRange_duration_eventTrace
  intro index selected
  fin_cases index
  all_goals change (BitWord.instruction (execution := model) _).Path at selected
  all_goals change (BitWord.instruction (execution := model) _).depth duration selected =
    ((((BitWord.instruction (execution := model) _).eventTrace selected).map duration).sum)
  all_goals rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_eventTrace]
  all_goals simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Unit native durations give the original five classifier stages. -/
theorem classifierBody_unitDepth (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width)
    (path : (classifierBody (model := model) left right classifier).Path) :
    (classifierBody (model := model) left right classifier).depth (fun _ => 1) path = 5 := by
  rw [classifierBody_depth]
  rfl

/-- Classifier instructions allocate no additional context entries. -/
theorem classifierBody_resident (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width)
    (path : (classifierBody (model := model) left right classifier).Path) :
    (classifierBody (model := model) left right classifier).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.forRange_resident_le 5 _ _ le_rfl _ path
  intro index selected
  fin_cases index <;> exact (Circuit.peakResidentSpace_classical _ selected).le

/-- Every live classifier cell remains charged according to its actual workspace role. -/
theorem classifierBody_auxiliary (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width)
    (path : (classifierBody (model := model) left right classifier).Path) :
    (classifierBody (model := model) left right classifier).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.forRange_auxiliary_le 5 _ _ le_rfl _ path
  intro index selected
  fin_cases index <;> exact (Circuit.peakAuxiliarySpace_classical _ selected).le

omit [BitWord.Selected model] in
/-- Both full raw points, the zero word and all three classifier bits have their actual widths. -/
theorem classifierShapes_classicalBits :
    (((classifierShapes width).map (SpacePool.ofShape (kind := model.kind))).sum) .classicalBits =
      5 * width + 5 := by
  simp [classifierShapes, PointEquality.RawPointShape, SpacePool.ofShape, CShape.bitWidth]
  omega

/-- The allocated classifier and continuation are charged with all six live workspace shapes. -/
theorem withClassification_resident (left right : CInputRef ctx (PointShape width))
    (body : ∀ {inner : RuntimeCtx model.kind}, Classifier inner width →
      Transport ctx inner → Circuit model inner inner)
    (additional : SpacePool model.kind)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (classifier : Classifier inner width)
      (transport : Transport ctx inner) (path : (body classifier transport).Path),
      (body classifier transport).peakResidentSpace path ≤ additional + inner.residentSpace)
    (path : (withClassification left right body).Path) :
    (withClassification left right body).peakResidentSpace path ≤
      ((classifierShapes width).map SpacePool.ofShape).sum + additional + ctx.residentSpace := by
  apply withCellsFrom_resident_le (Transport.id ctx) (classifierShapes width)
    (fun cells _ transport _ =>
      .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells)) (body (classifierOfCells cells) transport)) additional _ path
  intro inner cells _ transport _ selected
  change Circuit.peak RuntimeCtx.residentSpace
    ((classifierBody _ _ _).visitedContexts selected.1 ++
      (body _ _).visitedContexts selected.2) ≤ _
  rw [Circuit.peak_append]
  exact SpacePool.max_le
    ((classifierBody_resident _ _ _ selected.1).trans (le_add_of_nonneg_left zero_le))
    (bodyBound (classifierOfCells cells) transport selected.2)

/-- All classifier temporaries retain their actual auxiliary roles through the continuation. -/
theorem withClassification_auxiliary (left right : CInputRef ctx (PointShape width))
    (body : ∀ {inner : RuntimeCtx model.kind}, Classifier inner width →
      Transport ctx inner → Circuit model inner inner)
    (additional : SpacePool model.kind)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (classifier : Classifier inner width)
      (transport : Transport ctx inner) (path : (body classifier transport).Path),
      (body classifier transport).peakAuxiliarySpace path ≤ additional + inner.auxiliarySpace)
    (path : (withClassification left right body).Path) :
    (withClassification left right body).peakAuxiliarySpace path ≤
      ((classifierShapes width).map SpacePool.ofShape).sum + additional + ctx.auxiliarySpace := by
  apply withCellsFrom_auxiliary_le (Transport.id ctx) (classifierShapes width)
    (fun cells _ transport _ =>
      .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells)) (body (classifierOfCells cells) transport)) additional _ path
  intro inner cells _ transport _ selected
  change Circuit.peak RuntimeCtx.auxiliarySpace
    ((classifierBody _ _ _).visitedContexts selected.1 ++
      (body _ _).visitedContexts selected.2) ≤ _
  rw [Circuit.peak_append]
  exact SpacePool.max_le
    ((classifierBody_auxiliary _ _ _ selected.1).trans (le_add_of_nonneg_left zero_le))
    (bodyBound (classifierOfCells cells) transport selected.2)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
