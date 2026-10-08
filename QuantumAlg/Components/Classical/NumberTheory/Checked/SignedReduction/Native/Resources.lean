/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native

/-!
# Actual complete signed-reduction resources

The two real stored-sign branch sites retain their selected event lists.
All three persistent cells coexist with the active division or correction
scratch. The space maximum counts these actual scopes and every caller entry.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original chronological events for the two actual branch values. -/
def signedReductionEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat)
    (magnitudeNegative correctionNegative : Bool) : List (Resource.Event model) :=
  signClassificationEvents model width ++
    (signedMagnitudeEvents model width magnitudeNegative ++
      (reductionEvents model (signedWidth width) width ++
        finalCorrectionEvents model width correctionNegative))

/-- The actual body retains all four original phase traces. -/
theorem signedReductionBody_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width))
    (path : (signedReductionBody (model := model) raw modulus work negative remainder
      output).Path) :
    (signedReductionBody (model := model) raw modulus work negative remainder output).eventTrace
      path =
      signedReductionEvents model width path.2.1.1.toBool path.2.2.2.1.toBool := by
  change (signClassification (model := model) raw work negative).eventTrace path.1 ++
    ((signedMagnitude (model := model) raw work (signedRead negative)).eventTrace path.2.1 ++
      ((reduceWord (model := model) (signedRead work) modulus remainder).eventTrace path.2.2.1 ++
        (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
          output).eventTrace
          path.2.2.2)) = _
  rw [signClassification_eventTrace, signedMagnitude_eventTrace, reduceWord_eventTrace,
    finalCorrection_eventTrace]
  rfl

/-- Real lexical allocation and release add no events to the original signed-reduction trace. -/
theorem withSignedReduction_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).eventTrace path =
      signedReductionEvents model width path.2.1.1.toBool path.2.2.2.1.toBool :=
  signedReductionBody_eventTrace _ _ _ _ _ _ path

/-- Complete native event multiplicities are derived from that same actual path. -/
theorem withSignedReduction_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).resourcePool path =
      ResourcePool.ofList
      (signedReductionEvents model width path.2.1.1.toBool path.2.2.2.1.toBool) :=
  congrArg ResourcePool.ofList (withSignedReduction_eventTrace raw modulus output path)

/-- All selected operations retain their original sequential duration dependencies. -/
theorem signedReductionBody_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (signedReductionBody (model := model) raw modulus work negative remainder
      output).Path) :
    (signedReductionBody (model := model) raw modulus work negative remainder output).depth
      duration path =
      ((signedReductionEvents model width path.2.1.1.toBool path.2.2.2.1.toBool).map
        duration).sum := by
  change (signClassification (model := model) raw work negative).depth duration path.1 +
    ((signedMagnitude (model := model) raw work (signedRead negative)).depth duration path.2.1 +
      ((reduceWord (model := model) (signedRead work) modulus remainder).depth duration path.2.2.1 +
        (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
          output).depth
          duration path.2.2.2)) = _
  rw [signClassification_durationDepth, signedMagnitude_durationDepth, reduceWord_durationDepth,
    finalCorrection_durationDepth]
  simp only [signedReductionEvents, List.map_append, List.sum_append, reductionEvents,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The actual three persistent scopes preserve the body's exact duration equation. -/
theorem withSignedReduction_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).depth duration path =
      ((signedReductionEvents model width path.2.1.1.toBool path.2.2.2.1.toBool).map
        duration).sum :=
  signedReductionBody_durationDepth _ _ _ _ _ _ duration path

/-- Simultaneous temporary arithmetic space for the actual final-correction branch. -/
def signedReductionArithmeticSpace {kind : ProblemKind} (width : Nat)
    (correctionNegative : Bool) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (divisionShape (signedWidth width) width))
    (if correctionNegative then negativeCorrectionScratchSpace width else 0)

/-- The three actual persistent cells and the maximum active arithmetic scope. -/
def signedReductionScratchSpace {kind : ProblemKind} (width : Nat)
    (correctionNegative : Bool) : SpacePool kind :=
  signedReductionArithmeticSpace width correctionNegative +
    SpacePool.ofShape (.unsignedWord width) + SpacePool.ofShape .bit +
      SpacePool.ofShape (.unsignedWord (signedWidth width))

private theorem signedBody_peak_max {kind : ProblemKind}
    (context division correction : SpacePool kind) :
    SpacePool.max context (SpacePool.max context
      (SpacePool.max (division + context) (correction + context))) =
        SpacePool.max division correction + context := by
  funext axis
  change max (context axis) (max (context axis)
    (max (division axis + context axis) (correction axis + context axis))) =
      max (division axis) (correction axis) + context axis
  omega

private theorem signedScope_peak_max (a b c d e : Nat) :
    Nat.max e (Nat.max (d + e) (Nat.max (c + (d + e)) (a + (b + (c + (d + e)))))) =
      a + b + c + d + e := by
  change max e (max (d + e) (max (c + (d + e)) (a + (b + (c + (d + e)))))) = _
  omega

/-- The exact body resident peak is the larger actual arithmetic scope plus its entire context. -/
theorem signedReductionBody_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width))
    (path : (signedReductionBody (model := model) raw modulus work negative remainder
      output).Path) :
    (signedReductionBody (model := model) raw modulus work negative remainder
      output).peakResidentSpace path =
      signedReductionArithmeticSpace width path.2.2.2.1.toBool + ctx.residentSpace := by
  have first := Circuit.peakResidentSpace_seq (signClassification (model := model) raw work
    negative)
    (.seq (signedMagnitude (model := model) raw work (signedRead negative))
      (.seq (reduceWord (model := model) (signedRead work) modulus remainder)
        (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
          output))) path
  have second := Circuit.peakResidentSpace_seq (signedMagnitude (model := model) raw work
    (signedRead negative))
    (.seq (reduceWord (model := model) (signedRead work) modulus remainder)
      (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
        output)) path.2
  have third := Circuit.peakResidentSpace_seq (reduceWord (model := model) (signedRead work)
    modulus remainder)
    (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
      output) path.2.2
  exact first.trans ((congrArg₂ SpacePool.max (signClassification_resident _ _ _ _)
    (second.trans (congrArg₂ SpacePool.max (signedMagnitude_resident _ _ _ _)
      (third.trans (congrArg₂ SpacePool.max (reduceWord_resident _ _ _ _)
        (finalCorrection_resident _ _ _ _ _)))))).trans (signedBody_peak_max _ _ _))

/-- The same actual contexts give the exact auxiliary peak. -/
theorem signedReductionBody_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width))
    (path : (signedReductionBody (model := model) raw modulus work negative remainder
      output).Path) :
    (signedReductionBody (model := model) raw modulus work negative remainder
      output).peakAuxiliarySpace path =
      signedReductionArithmeticSpace width path.2.2.2.1.toBool + ctx.auxiliarySpace := by
  have first := Circuit.peakAuxiliarySpace_seq (signClassification (model := model) raw work
    negative)
    (.seq (signedMagnitude (model := model) raw work (signedRead negative))
      (.seq (reduceWord (model := model) (signedRead work) modulus remainder)
        (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
          output))) path
  have second := Circuit.peakAuxiliarySpace_seq (signedMagnitude (model := model) raw work
    (signedRead negative))
    (.seq (reduceWord (model := model) (signedRead work) modulus remainder)
      (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
        output)) path.2
  have third := Circuit.peakAuxiliarySpace_seq (reduceWord (model := model) (signedRead work)
    modulus remainder)
    (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
      output) path.2.2
  exact first.trans ((congrArg₂ SpacePool.max (signClassification_auxiliary _ _ _ _)
    (second.trans (congrArg₂ SpacePool.max (signedMagnitude_auxiliary _ _ _ _)
      (third.trans (congrArg₂ SpacePool.max (reduceWord_auxiliary _ _ _ _)
        (finalCorrection_auxiliary _ _ _ _ _)))))).trans (signedBody_peak_max _ _ _))

/-- Actual resident peak includes every persistent cell and the selected active arithmetic scope. -/
theorem withSignedReduction_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).peakResidentSpace path =
      signedReductionScratchSpace width path.2.2.2.1.toBool + ctx.residentSpace := by
  dsimp only [withSignedReduction, withCells, signedReductionShapes, withCellsFrom] at path ⊢
  erw [Circuit.peakResidentSpace_workspace, Circuit.peakResidentSpace_workspace,
    Circuit.peakResidentSpace_workspace, signedReductionBody_resident]
  simp only [RuntimeCtx.residentSpace_addWorkspace, signedReductionScratchSpace]
  funext axis
  simp only [SpacePool.max, Pi.add_apply]
  exact signedScope_peak_max _ _ _ _ _

/-- Actual auxiliary peak follows the same three genuine allocation and release scopes. -/
theorem withSignedReduction_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).peakAuxiliarySpace path =
      signedReductionScratchSpace width path.2.2.2.1.toBool + ctx.auxiliarySpace := by
  dsimp only [withSignedReduction, withCells, signedReductionShapes, withCellsFrom] at path ⊢
  erw [Circuit.peakAuxiliarySpace_workspace, Circuit.peakAuxiliarySpace_workspace,
    Circuit.peakAuxiliarySpace_workspace, signedReductionBody_auxiliary]
  simp only [RuntimeCtx.auxiliarySpace_addWorkspace, signedReductionScratchSpace]
  funext axis
  simp only [SpacePool.max, Pi.add_apply]
  exact signedScope_peak_max _ _ _ _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
