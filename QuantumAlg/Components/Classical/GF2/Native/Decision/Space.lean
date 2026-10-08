/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact actual space of the original GF(2) decisions

Both complete circuits allocate the same original word and then bit.
The candidate check retains the original unused word. All caller context
roles remain counted, including width zero; neither branch allocates more.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private theorem failure_resident (success : CWriteRef ctx .bit)
    (path : (markFailure success).Path) :
    (markFailure success).peakResidentSpace path = ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success)) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_classical, SpacePool.max_self]

private theorem choice_resident (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).peakResidentSpace path = ctx.residentSpace := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · exact failure_resident success path
      · exact SpacePool.max_zero _
      · exact SpacePool.max_zero _
      · exact failure_resident success path

private theorem test_resident (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).peakResidentSpace path = ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success)) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical]
  exact (congrArg (SpacePool.max ctx.residentSpace)
    (choice_resident reject success path.2.1 path.2.2)).trans (SpacePool.max_self _)

private theorem uniqueBody_resident (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).peakResidentSpace path = ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag))) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq]
  rw [test_resident, test_resident]
  simp only [SpacePool.max_self]

/-- Both original decision cells and all caller resident roles are simultaneously present. -/
theorem gf2UniqueFree_resident (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).peakResidentSpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace) := by
  have body : (placedUniqueFree free zero success).peakResidentSpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace) :=
    uniqueBody_resident _ _ _ _ _ path
  have inner := (Circuit.peakResidentSpace_workspace (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
    (placedUniqueFree free zero success) path).trans
      (congrArg (SpacePool.max (pivotMaskContext ctx width).residentSpace) body)
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scopedUniqueFree free zero success) path).trans ?_
  refine (congrArg (SpacePool.max ctx.residentSpace) inner).trans ?_
  apply SpacePool.ext
  intro axis
  change max (ctx.residentSpace axis)
      (max (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis)
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis))) =
    SpacePool.ofShape .bit axis +
      (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis)
  omega

/-- Both original decision cells and all caller resident roles are simultaneously present. -/
theorem gf2CandidateNonzero_resident (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).peakResidentSpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace) := by
  have body : (placedCandidateNonzero candidate zero success).peakResidentSpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace) :=
    test_resident true _ _ _ _ path
  have inner := (Circuit.peakResidentSpace_workspace (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
    (placedCandidateNonzero candidate zero success) path).trans
      (congrArg (SpacePool.max (pivotMaskContext ctx width).residentSpace) body)
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scopedCandidateNonzero candidate zero success) path).trans ?_
  refine (congrArg (SpacePool.max ctx.residentSpace) inner).trans ?_
  apply SpacePool.ext
  intro axis
  change max (ctx.residentSpace axis)
      (max (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis)
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis))) =
    SpacePool.ofShape .bit axis +
      (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis)
  omega

private theorem failure_auxiliary (success : CWriteRef ctx .bit)
    (path : (markFailure success).Path) :
    (markFailure success).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success)) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_classical,
    SpacePool.max_self]

private theorem choice_auxiliary (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · exact failure_auxiliary success path
      · exact SpacePool.max_zero _
      · exact SpacePool.max_zero _
      · exact failure_auxiliary success path

private theorem test_auxiliary (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success)) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical]
  exact (congrArg (SpacePool.max ctx.auxiliarySpace)
    (choice_auxiliary reject success path.2.1 path.2.2)).trans (SpacePool.max_self _)

private theorem uniqueBody_auxiliary (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag))) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq]
  rw [test_auxiliary, test_auxiliary]
  simp only [SpacePool.max_self]

/-- Both original decision cells and all caller auxiliary roles are simultaneously present. -/
theorem gf2UniqueFree_auxiliary (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).peakAuxiliarySpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace) := by
  have body : (placedUniqueFree free zero success).peakAuxiliarySpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace) :=
    uniqueBody_auxiliary _ _ _ _ _ path
  have inner := (Circuit.peakAuxiliarySpace_workspace (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
    (placedUniqueFree free zero success) path).trans
      (congrArg (SpacePool.max (pivotMaskContext ctx width).auxiliarySpace) body)
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scopedUniqueFree free zero success) path).trans ?_
  refine (congrArg (SpacePool.max ctx.auxiliarySpace) inner).trans ?_
  apply SpacePool.ext
  intro axis
  change max (ctx.auxiliarySpace axis)
      (max (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis)
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis))) =
    SpacePool.ofShape .bit axis +
      (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis)
  omega

/-- Both original decision cells and all caller auxiliary roles are simultaneously present. -/
theorem gf2CandidateNonzero_auxiliary (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).peakAuxiliarySpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace) := by
  have body : (placedCandidateNonzero candidate zero success).peakAuxiliarySpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace) :=
    test_auxiliary true _ _ _ _ path
  have inner := (Circuit.peakAuxiliarySpace_workspace (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
    (placedCandidateNonzero candidate zero success) path).trans
      (congrArg (SpacePool.max (pivotMaskContext ctx width).auxiliarySpace) body)
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scopedCandidateNonzero candidate zero success) path).trans ?_
  refine (congrArg (SpacePool.max ctx.auxiliarySpace) inner).trans ?_
  apply SpacePool.ext
  intro axis
  change max (ctx.auxiliarySpace axis)
      (max (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis)
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis))) =
    SpacePool.ofShape .bit axis +
      (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis)
  omega

end QuantumAlg.ClassicalRoutines.GF2.Native
