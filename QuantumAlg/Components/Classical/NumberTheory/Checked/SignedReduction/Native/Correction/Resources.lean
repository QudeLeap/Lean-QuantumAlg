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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original four-event negative correction at its exact operand widths. -/
def negativeCorrectionEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.wordBinary .sub (width + 1))] ++ reductionEvents kind (width + 1) width

/-- The actual path emits the original resize, subtraction, division and remainder resize. -/
theorem withNegativeCorrection_eventTrace (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).eventTrace path =
      negativeCorrectionEvents kind width := rfl

/-- Multiplicities come from the same four real instructions. -/
theorem withNegativeCorrection_resourcePool (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).resourcePool path =
      ResourcePool.ofList (negativeCorrectionEvents kind width) := rfl

/-- Any native duration assignment retains all original chronological dependencies. -/
theorem withNegativeCorrection_durationDepth (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).depth duration path =
      ((negativeCorrectionEvents kind width).map duration).sum := rfl

/-- Exactly four dependent unit-duration instructions execute. -/
theorem withNegativeCorrection_depth (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).depth (fun _ => 1) path = 4 := rfl

/-- Complete actual visits include the matching division-pair and widened-word releases. -/
theorem withNegativeCorrection_visitedContexts (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).visitedContexts path =
      [ctx, correctionCtx ctx width, correctionCtx ctx width, correctionCtx ctx width,
        reductionCtx (correctionCtx ctx width) (width + 1) width,
        reductionCtx (correctionCtx ctx width) (width + 1) width,
        correctionCtx ctx width, ctx] := rfl

/-- Actual simultaneous scratch shapes, including both complete quotient and remainder words. -/
def negativeCorrectionScratchSpace {kind : ProblemKind} (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (divisionShape (width + 1) width) +
    SpacePool.ofShape (.unsignedWord (width + 1))

/-- The actual two-scope scratch occupies three widened words. -/
theorem negativeCorrectionScratchSpace_eq_bits (kind : ProblemKind) (width : Nat) :
    negativeCorrectionScratchSpace (kind := kind) width =
      SpacePool.ofShape (.bits (3 * (width + 1))) := by
  funext axis
  cases axis <;> simp [negativeCorrectionScratchSpace, divisionShape, SpacePool.ofShape]
  omega

private theorem correctionVisits_member {α : Type} (a b c x : α)
    (present : x ∈ [a, b, b, b, c, c, b, a]) : x = a ∨ x = b ∨ x = c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  tauto

/-- The actual resident peak is exactly both scratch scopes plus all original context entries. -/
theorem withNegativeCorrection_resident (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).peakResidentSpace path =
      negativeCorrectionScratchSpace width + ctx.residentSpace := by
  have upper : (withNegativeCorrection remainder modulus output).peakResidentSpace path ≤
      (reductionCtx (correctionCtx ctx width) (width + 1) width).residentSpace := by
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rw [withNegativeCorrection_visitedContexts] at present
    rcases correctionVisits_member _ _ _ visited present with rfl | rfl | rfl
    all_goals
      intro axis
      cases axis <;> simp [correctionCtx, reductionCtx, divisionShape, SpacePool.ofShape]
      all_goals omega
  have present : reductionCtx (correctionCtx ctx width) (width + 1) width ∈
      (withNegativeCorrection remainder modulus output).visitedContexts path := by
    rw [withNegativeCorrection_visitedContexts]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have lower := (withNegativeCorrection remainder modulus output).residentSpace_le_peak_of_visited
    path _ present
  exact (le_antisymm upper lower).trans (by
    simp only [correctionCtx, reductionCtx, RuntimeCtx.residentSpace_addWorkspace,
      negativeCorrectionScratchSpace, add_assoc])

/-- The same real visits give the exact auxiliary peak including both complete scratch cells. -/
theorem withNegativeCorrection_auxiliary (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withNegativeCorrection remainder modulus output).Path) :
    (withNegativeCorrection remainder modulus output).peakAuxiliarySpace path =
      negativeCorrectionScratchSpace width + ctx.auxiliarySpace := by
  have upper : (withNegativeCorrection remainder modulus output).peakAuxiliarySpace path ≤
      (reductionCtx (correctionCtx ctx width) (width + 1) width).auxiliarySpace := by
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rw [withNegativeCorrection_visitedContexts] at present
    rcases correctionVisits_member _ _ _ visited present with rfl | rfl | rfl
    all_goals
      intro axis
      cases axis <;> simp [correctionCtx, reductionCtx, divisionShape, SpacePool.ofShape]
      all_goals omega
  have present : reductionCtx (correctionCtx ctx width) (width + 1) width ∈
      (withNegativeCorrection remainder modulus output).visitedContexts path := by
    rw [withNegativeCorrection_visitedContexts]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have lower := (withNegativeCorrection remainder modulus output).auxiliarySpace_le_peak_of_visited
    path _ present
  exact (le_antisymm upper lower).trans (by
    simp only [correctionCtx, reductionCtx, RuntimeCtx.auxiliarySpace_addWorkspace,
      negativeCorrectionScratchSpace, add_assoc])

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
