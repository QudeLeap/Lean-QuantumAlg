/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale.Correctness
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Exact actual frequency-scaling space and duration

The measured peaks include all original context entries and all three live
scratch cells at their actual shapes. The bound is attained inside the real
arithmetic body. Duration follows the same native loader, multiplication,
division and resize sequence, for arbitrary event durations.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

/-- The actual denominator, complete product and complete division-results storage. -/
def scaleScratchSpace {kind : ProblemKind} (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (scaleDivisionShape width) +
    SpacePool.ofShape (.unsignedWord (width + (width + 1))) +
    SpacePool.ofShape (.unsignedWord (width + 1))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma scalePrepared_visited (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scalePrepared (model := model) raw modulus output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (scalePrepared (model := model) raw modulus output).visitedContexts path) :
    visited = scaleCtx ctx width := by
  change visited ∈ ([scaleCtx ctx width] ++
    (Word.PowerOfTwo.shiftInto (model := model) width
      (scaleDenominatorCell ctx width)).visitedContexts path.1.2) ++
    ([scaleCtx ctx width] ++ ([scaleCtx ctx width] ++ [scaleCtx ctx width])) at present
  simp only [List.mem_append, List.mem_singleton, or_self] at present
  have shift : visited ∈
      (Word.PowerOfTwo.shiftInto (model := model) width
      (scaleDenominatorCell ctx width)).visitedContexts path.1.2 →
      visited = scaleCtx ctx width :=
    Word.PowerOfTwo.shiftInto_visited width (scaleDenominatorCell ctx width) path.1.2 visited
  tauto

private lemma withScale_visited (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (withScale (model := model) raw modulus output).visitedContexts path) :
    visited = ctx ∨ visited = scaleDenominatorCtx ctx width ∨
      visited = scaleProductCtx ctx width ∨ visited = scaleCtx ctx width := by
  change visited ∈ ctx ::
    ((scaleDenominatorCtx ctx width) ::
      ((scaleProductCtx ctx width) ::
        (scalePrepared (model := model) raw modulus output).visitedContexts path ++
          [scaleProductCtx ctx width]) ++
      [scaleDenominatorCtx ctx width]) ++ [ctx] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at present
  have body : visited ∈ (scalePrepared (model := model) raw modulus output).visitedContexts path →
      visited = scaleCtx ctx width := scalePrepared_visited raw modulus output path visited
  tauto

private lemma withScale_scoped_mem (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) :
    scaleCtx ctx width ∈ (withScale (model := model) raw modulus output).visitedContexts path := by
  change scaleCtx ctx width ∈ ctx ::
    ((scaleDenominatorCtx ctx width) ::
      ((scaleProductCtx ctx width) ::
        (scalePrepared (model := model) raw modulus output).visitedContexts path ++
          [scaleProductCtx ctx width]) ++
      [scaleDenominatorCtx ctx width]) ++ [ctx]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  have body := (scalePrepared (model := model) raw modulus output).input_mem_visitedContexts path
  tauto

/-- Exact resident peak includes each original live entry and all three real scratch shapes. -/
lemma withScale_resident (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) :
    (withScale (model := model) raw modulus output).peakResidentSpace path =
      scaleScratchSpace width + ctx.residentSpace := by
  have upper : (withScale (model := model) raw modulus output).peakResidentSpace path ≤
      (scaleCtx ctx width).residentSpace := by
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rcases withScale_visited raw modulus output path visited present with
      same | same | same | same
    · subst visited
      intro axis
      change ctx.residentSpace axis ≤
        SpacePool.ofShape (scaleDivisionShape width) axis +
          (SpacePool.ofShape (.unsignedWord (width + (width + 1))) axis +
            (SpacePool.ofShape (.unsignedWord (width + 1)) axis + ctx.residentSpace axis))
      omega
    · subst visited
      intro axis
      change _ ≤ SpacePool.ofShape (scaleDivisionShape width) axis +
        (SpacePool.ofShape (.unsignedWord (width + (width + 1))) axis +
          (scaleDenominatorCtx ctx width).residentSpace axis)
      omega
    · subst visited
      intro axis
      change _ ≤ SpacePool.ofShape (scaleDivisionShape width) axis +
        (scaleProductCtx ctx width).residentSpace axis
      omega
    · exact same ▸ le_rfl
  have lower := (withScale (model := model) raw modulus output).residentSpace_le_peak_of_visited
    path
    (scaleCtx ctx width) (withScale_scoped_mem raw modulus output path)
  exact (le_antisymm upper lower).trans (by
    simp only [scaleCtx, scaleProductCtx, scaleDenominatorCtx,
      RuntimeCtx.residentSpace_addWorkspace, scaleScratchSpace, add_assoc])

/-- Exact auxiliary peak charges those same scratch cells beside all existing auxiliary roles. -/
lemma withScale_auxiliary (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) :
    (withScale (model := model) raw modulus output).peakAuxiliarySpace path =
      scaleScratchSpace width + ctx.auxiliarySpace := by
  have upper : (withScale (model := model) raw modulus output).peakAuxiliarySpace path ≤
      (scaleCtx ctx width).auxiliarySpace := by
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rcases withScale_visited raw modulus output path visited present with
      same | same | same | same
    · subst visited
      intro axis
      change ctx.auxiliarySpace axis ≤
        SpacePool.ofShape (scaleDivisionShape width) axis +
          (SpacePool.ofShape (.unsignedWord (width + (width + 1))) axis +
            (SpacePool.ofShape (.unsignedWord (width + 1)) axis + ctx.auxiliarySpace axis))
      omega
    · subst visited
      intro axis
      change _ ≤ SpacePool.ofShape (scaleDivisionShape width) axis +
        (SpacePool.ofShape (.unsignedWord (width + (width + 1))) axis +
          (scaleDenominatorCtx ctx width).auxiliarySpace axis)
      omega
    · subst visited
      intro axis
      change _ ≤ SpacePool.ofShape (scaleDivisionShape width) axis +
        (scaleProductCtx ctx width).auxiliarySpace axis
      omega
    · exact same ▸ le_rfl
  have lower := (withScale (model := model) raw modulus output).auxiliarySpace_le_peak_of_visited
    path
    (scaleCtx ctx width) (withScale_scoped_mem raw modulus output path)
  exact (le_antisymm upper lower).trans (by
    simp only [scaleCtx, scaleProductCtx, scaleDenominatorCtx,
      RuntimeCtx.auxiliarySpace_addWorkspace, scaleScratchSpace, add_assoc])

/-- Exact serial depth for arbitrary durations follows every original native dependency. -/
lemma withScale_durationDepth (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (withScale (model := model) raw modulus output).Path) :
    (withScale (model := model) raw modulus output).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .increment (width + 1)))) +
        width * duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .shiftLeft (width + 1)))) +
        (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.mulFull width (width + 1)))) +
          (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.divRem (width + (width + 1)) (width + 1)))) +
            duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
              (.wordResize (width + (width + 1)) width))))) := by
  change ((BitWord.instruction (execution := model)
    (Word.PowerOfTwo.incrementOp (scaleDenominatorCell ctx width))).depth duration path.1.1 +
    (0 + ∑ index : Fin width, (BitWord.instruction (execution := model)
      (Word.PowerOfTwo.shiftOp (scaleDenominatorCell ctx width))).depth duration
        (path.1.2 index))) +
    ((BitWord.instruction (execution := model)
      (scaleProductOp (underScale raw width) (underScale modulus width)
        (scaleProductCell ctx width))).depth duration path.2.1 +
      ((BitWord.instruction (execution := model)
        (scaleDivisionOp (scaleProductCell ctx width) (scaleRead (scaleDenominatorCell ctx width))
          (scaleDivisionCell ctx width))).depth duration path.2.2.1 +
        (BitWord.instruction (execution := model)
          (scaleQuotientOp (scaleDivisionCell ctx width) (writeUnderScale output width))).depth
            duration path.2.2.2)) = _
  simp only [BitWord.bitWord_instruction_depth]
  simp [Word.PowerOfTwo.incrementOp, Word.PowerOfTwo.shiftOp, scaleProductOp,
    scaleDivisionOp, scaleQuotientOp, ClassicalOp.label]

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
