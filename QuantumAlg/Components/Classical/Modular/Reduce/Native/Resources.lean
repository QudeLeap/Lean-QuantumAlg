/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.Reduce.Native
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact native remainder-reduction resources

The original division and remainder resize are both charged. The single
actual quotient/remainder pair contributes its full shape beside every
original context entry and is released before returning to the caller.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.Reduce.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- Original two native events with their actual operand widths. -/
def reductionEvents (model : ExecutionModel) [BitWord.Selected model] (sourceWidth width : Nat) :
  List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem sourceWidth (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))]

/-- Every actual path emits exactly the original division and remainder resize. -/
lemma reduceWord_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    (reduceWord (model := model) numerator modulus output).eventTrace path =
      reductionEvents model sourceWidth width := by
  change (BitWord.instruction (execution := model)
    (reductionDivideOp (underReduction numerator sourceWidth width)
      (underReduction modulus sourceWidth width) (divisionCell ctx sourceWidth width))).eventTrace
        path.1 ++ (BitWord.instruction (execution := model)
          (reductionResizeOp (divisionCell ctx sourceWidth width)
            (writeUnderReduction output sourceWidth width))).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The native pool is obtained from the actual two-operation path. -/
lemma reduceWord_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    (reduceWord (model := model) numerator modulus output).resourcePool path =
      ResourcePool.ofList (reductionEvents model sourceWidth width) :=
  congrArg ResourcePool.ofList (reduceWord_eventTrace numerator modulus output path)

/-- Exactly two native operations are charged, with no hidden modulus loading. -/
lemma reduceWord_eventCount {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    ((reduceWord (model := model) numerator modulus output).eventTrace path).length = 2 := by
  rw [reduceWord_eventTrace]
  rfl

/-- Arbitrary native durations retain the original division-to-remainder dependency. -/
lemma reduceWord_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    (reduceWord (model := model) numerator modulus output).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem sourceWidth (width + 1)))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))) := by
  rcases path with ⟨first, second⟩
  change (reductionBody (model := model) (underReduction numerator sourceWidth width)
    (underReduction modulus sourceWidth width) (divisionCell ctx sourceWidth width)
    (writeUnderReduction output sourceWidth width)).depth duration (first, second) = _
  simp only [reductionBody, Circuit.depth_seq, BitWord.bitWord_instruction_depth]
  rfl

/-- Unit-duration depth equals the two original serial instructions. -/
lemma reduceWord_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    (reduceWord (model := model) numerator modulus output).depth (fun _ => 1) path = 2 := rfl

/-- Exact resident peak counts the real full division pair and every original context entry. -/
lemma reduceWord_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    (reduceWord (model := model) numerator modulus output).peakResidentSpace path =
      SpacePool.ofShape (divisionShape sourceWidth width) + ctx.residentSpace := by
  have bodyPeak : (reductionPlaced (model := model) numerator modulus output).peakResidentSpace
    path =
      (reductionCtx ctx sourceWidth width).residentSpace := by
    change SpacePool.max (reductionCtx ctx sourceWidth width).residentSpace
      (SpacePool.max (reductionCtx ctx sourceWidth width).residentSpace 0) = _
    simp only [SpacePool.max_zero, SpacePool.max_self]
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (divisionShape sourceWidth width) ctx.canonicalFreshKey_fresh
    (reductionPlaced (model := model) numerator modulus output) path).trans
      ((congrArg (SpacePool.max ctx.residentSpace) bodyPeak).trans ?_)
  exact SpacePool.max_eq_right le_add_self

/-- Exact auxiliary peak counts the real full division pair and every original context entry. -/
lemma reduceWord_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord (model := model) numerator modulus output).Path) :
    (reduceWord (model := model) numerator modulus output).peakAuxiliarySpace path =
      SpacePool.ofShape (divisionShape sourceWidth width) + ctx.auxiliarySpace := by
  have bodyPeak : (reductionPlaced (model := model) numerator modulus output).peakAuxiliarySpace
    path =
      (reductionCtx ctx sourceWidth width).auxiliarySpace := by
    change SpacePool.max (reductionCtx ctx sourceWidth width).auxiliarySpace
      (SpacePool.max (reductionCtx ctx sourceWidth width).auxiliarySpace 0) = _
    simp only [SpacePool.max_zero, SpacePool.max_self]
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (divisionShape sourceWidth width) ctx.canonicalFreshKey_fresh
    (reductionPlaced (model := model) numerator modulus output) path).trans
      ((congrArg (SpacePool.max ctx.auxiliarySpace) bodyPeak).trans ?_)
  exact SpacePool.max_eq_right le_add_self

end

end QuantumAlg.ClassicalRoutines.Modular.Reduce.Native
