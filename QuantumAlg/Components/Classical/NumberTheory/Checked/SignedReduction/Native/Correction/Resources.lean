/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Correction
import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Resources

/-!
# Native signed-correction resources

The actual negative arm retains the original four events and both lexical
scratch scopes. Its temporary storage is the widened remainder together with
the real division pair, while all original context entries remain live.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution Modular.Reduce.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original four-event negative correction at its exact operand widths. -/
def negativeCorrectionEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
  List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub (width + 1)))] ++ reductionEvents model (width + 1) width

/-- The actual path emits the original resize, subtraction, division and remainder resize. -/
lemma withNegativeCorrection_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).eventTrace path =
      negativeCorrectionEvents model width := by
  change (BitWord.instruction (execution := model)
    (correctionResizeOp (underCorrection remainder width)
      (correctionExtendedCell ctx width))).eventTrace path.1 ++
    ((BitWord.instruction (execution := model)
      (correctionSubtractOp (underCorrection modulus width)
        (correctionExtendedCell ctx width))).eventTrace path.2.1 ++
      (reduceWord (model := model) (reductionRead (correctionExtendedCell ctx width))
        (underCorrection modulus width) (writeUnderCorrection output width)).eventTrace
          path.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    reduceWord_eventTrace]
  rfl

/-- Multiplicities come from the same four real instructions. -/
lemma withNegativeCorrection_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).resourcePool path =
      ResourcePool.ofList (negativeCorrectionEvents model width) :=
  congrArg ResourcePool.ofList (withNegativeCorrection_eventTrace remainder modulus output path)

/-- Any native duration assignment retains all original chronological dependencies. -/
lemma withNegativeCorrection_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).depth duration path =
      ((negativeCorrectionEvents model width).map duration).sum := by
  rcases path with ⟨first, second, rest⟩
  change (correctionBody (model := model) (underCorrection remainder width)
    (underCorrection modulus width) (correctionExtendedCell ctx width)
    (writeUnderCorrection output width)).depth duration (first, (second, rest)) = _
  simp only [correctionBody, Circuit.depth_seq, BitWord.bitWord_instruction_depth,
    reduceWord_durationDepth]
  simp only [negativeCorrectionEvents, reductionEvents, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- Exactly four dependent unit-duration instructions execute. -/
lemma withNegativeCorrection_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).depth (fun _ => 1) path =
      4 := rfl

/-- Complete actual visits include the matching division-pair and widened-word releases. -/
lemma withNegativeCorrection_visitedContexts {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).visitedContexts path =
      [ctx, correctionCtx ctx width, correctionCtx ctx width, correctionCtx ctx width,
        reductionCtx (correctionCtx ctx width) (width + 1) width,
        reductionCtx (correctionCtx ctx width) (width + 1) width,
        correctionCtx ctx width, ctx] := rfl

/-- Actual simultaneous scratch shapes, including both complete quotient and remainder words. -/
def negativeCorrectionScratchSpace {kind : ProblemKind} (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (divisionShape (width + 1) width) +
    SpacePool.ofShape (.unsignedWord (width + 1))

/-- The actual two-scope scratch occupies three widened words. -/
lemma negativeCorrectionScratchSpace_eq_bits (kind : ProblemKind) (width : Nat) :
    negativeCorrectionScratchSpace (kind := kind) width =
      SpacePool.ofShape (.bits (3 * (width + 1))) := by
  funext axis
  cases axis <;> simp [negativeCorrectionScratchSpace, divisionShape, SpacePool.ofShape]
  omega

private lemma correctionVisits_member {α : Type} (a b c x : α)
    (present : x ∈ [a, b, b, b, c, c, b, a]) : x = a ∨ x = b ∨ x = c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  tauto

/-- The actual resident peak is exactly both scratch scopes plus all original context entries. -/
lemma withNegativeCorrection_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).peakResidentSpace path =
      negativeCorrectionScratchSpace width + ctx.residentSpace := by
  have upper : (withNegativeCorrection (model := model) remainder modulus
    output).peakResidentSpace path ≤
      (reductionCtx (correctionCtx ctx width) (width + 1) width).residentSpace := by
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rw [withNegativeCorrection_visitedContexts] at present
    rcases correctionVisits_member _ _ _ visited present with rfl | rfl | rfl
    · exact le_trans le_add_self le_add_self
    · exact le_add_self
    · exact le_rfl
  have present : reductionCtx (correctionCtx ctx width) (width + 1) width ∈
      (withNegativeCorrection (model := model) remainder modulus output).visitedContexts path := by
    rw [withNegativeCorrection_visitedContexts]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have lower := (withNegativeCorrection (model := model) remainder modulus
    output).residentSpace_le_peak_of_visited
    path _ present
  exact (le_antisymm upper lower).trans (by
    simp only [correctionCtx, reductionCtx, RuntimeCtx.residentSpace_addWorkspace,
      negativeCorrectionScratchSpace, add_assoc])

/-- The same real visits give the exact auxiliary peak including both complete scratch cells. -/
lemma withNegativeCorrection_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection (model := model) remainder modulus output).Path) :
    (withNegativeCorrection (model := model) remainder modulus output).peakAuxiliarySpace path =
      negativeCorrectionScratchSpace width + ctx.auxiliarySpace := by
  have upper : (withNegativeCorrection (model := model) remainder modulus
    output).peakAuxiliarySpace path ≤
      (reductionCtx (correctionCtx ctx width) (width + 1) width).auxiliarySpace := by
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rw [withNegativeCorrection_visitedContexts] at present
    rcases correctionVisits_member _ _ _ visited present with rfl | rfl | rfl
    · exact le_trans le_add_self le_add_self
    · exact le_add_self
    · exact le_rfl
  have present : reductionCtx (correctionCtx ctx width) (width + 1) width ∈
      (withNegativeCorrection (model := model) remainder modulus output).visitedContexts path := by
    rw [withNegativeCorrection_visitedContexts]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have lower := (withNegativeCorrection (model := model) remainder modulus
    output).auxiliarySpace_le_peak_of_visited
    path _ present
  exact (le_antisymm upper lower).trans (by
    simp only [correctionCtx, reductionCtx, RuntimeCtx.auxiliarySpace_addWorkspace,
      negativeCorrectionScratchSpace, add_assoc])

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
