/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Trace
public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Core.Base.Accounting.Event
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Util.Classical.Modular.Basic

/-!
# Original preparation bounds on actual native paths

The independent budget retains the original decoder, exact modulus loader,
seed, two scaling triples and selected negation allowance. Serial durations
charge these same operations. Only the measured-value decoder allocates a
further packed bit cell; all other preparation operations use the supplied
thirteen live cells. Their outer allocation is charged by the caller.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original independent selected-negation allowance after the modulus resize. -/
def preparationFinalEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
  ResourcePool model :=
  ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))] +
    ResourcePool.max (ResourcePool.ofList (negateEvents model width true))
      (ResourcePool.ofList (negateEvents model width false))

/-- The unchanged original phases give an independent native preparation allowance. -/
public def preparationEnvelope (model : ExecutionModel) [BitWord.Selected model] (spec : ModulusSpec
  width) : ResourcePool model :=
  ((measuredDecodeEnvelope (model := model) (width + width) +
    ResourcePool.ofList (Word.Split.splitTrace (model := model) width width)) +
    (ResourcePool.ofList (ConstantWord.loaderTrace model (width + 1)
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))) +
        ResourcePool.ofList (preparationSeedEvents model width))) +
    ((ResourcePool.ofList (scaleBodyEvents (model := model) width) +
      ResourcePool.ofList (scaleBodyEvents (model := model) width)) + preparationFinalEnvelope
        model width)

/-- Each actual original preparation path fits the independent phase allowances. -/
lemma preparationBody_pool_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody (model := model) spec input
      refs).Path) :
    (preparationBody (model := model) spec input refs).resourcePool path ≤ preparationEnvelope
      model spec := by
  have loaded := congrArg ResourcePool.ofList (ConstantWord.constantFold_eventTrace (model :=
    model) refs.modulusWide
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.1.2.1)
  have selected : ResourcePool.ofList (negateEvents model width path.2.2.2.2.1.toBool) ≤
      ResourcePool.max (ResourcePool.ofList (negateEvents model width true))
        (ResourcePool.ofList (negateEvents model width false)) := by
    cases path.2.2.2.2.1.toBool
    · exact ResourcePool.le_max_right _ _
    · exact ResourcePool.le_max_left _ _
  change ResourcePool.ofList ((preparationBody (model := model) spec input refs).eventTrace
    path) ≤ _
  rw [preparationBody_eventTrace]
  simp only [ResourcePool.ofList_append]
  exact add_le_add
    (add_le_add (add_le_add (measuredDecodeInto_resourcePool_le input refs.decoded path.1.1.1)
      le_rfl) (add_le_add loaded.le le_rfl))
    (add_le_add le_rfl (add_le_add le_rfl selected))

/-- Independent duration bound retains all original serial dependencies and branch maxima. -/
public def preparationDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event model → Nat) : Nat :=
  ((duration (measuredPackEvent (model := model) (width + width)) + (width + width) *
      (duration (TerminalDecode.shiftEvent (model := model) (width + width)) +
        duration (TerminalDecode.incrementEvent (model := model) (width + width))) +
      (((Word.Split.splitTrace (model := model) width width).map duration).sum)) +
    (((ConstantWord.loaderTrace model (width + 1)
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))).map duration).sum +
        ((preparationSeedEvents model width).map duration).sum)) +
    ((((scaleBodyEvents (model := model) width).map duration).sum +
      ((scaleBodyEvents (model := model) width).map duration).sum) +
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))) +
        (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width))) +
          max (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width))))
            (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)))))))

private lemma split_duration (refs : Word.Split.Refs ctx width width)
    (duration : Resource.Event model → Nat) (path : (Word.Split.splitInto (model := model)
      refs).Path) :
    (Word.Split.splitInto (model := model) refs).depth duration path =
      ((Word.Split.splitTrace (model := model) width width).map duration).sum := by
  change (BitWord.instruction (execution := model) (Word.Split.lowOp refs)).depth
    duration path.1 + ((0 + ∑ index : Fin width,
      (BitWord.instruction (execution := model) (Word.Split.shiftOp refs.work)).depth
        duration (path.2.1 index)) +
      (BitWord.instruction (execution := model) (Word.Split.highOp refs)).depth
        duration path.2.2) = _
  simp only [BitWord.bitWord_instruction_depth]
  simp [Word.Split.splitTrace, Word.Split.shiftTrace, Word.Split.lowOp, Word.Split.highOp,
    Word.Split.shiftOp, ClassicalOp.label]

private lemma seed_duration (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event model → Nat) (path : (scaleSeed (model := model) denominator).Path) :
    (scaleSeed (model := model) denominator).depth duration path =
      ((preparationSeedEvents model width).map duration).sum := by
  change (BitWord.instruction (execution := model)
    (Word.PowerOfTwo.incrementOp denominator)).depth duration path.1 +
    (0 + ∑ index : Fin width,
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.shiftOp denominator)).depth
        duration (path.2 index)) = _
  simp only [BitWord.bitWord_instruction_depth]
  simp [preparationSeedEvents, Word.PowerOfTwo.shiftTrace, Word.PowerOfTwo.incrementOp,
    Word.PowerOfTwo.shiftOp, ClassicalOp.label]

private lemma scale_duration (refs : PreparationRefs ctx width)
    (duration : Resource.Event model → Nat) (path : (preparationScale (model := model) refs).Path) :
    (preparationScale (model := model) refs).depth duration path =
      ((scaleBodyEvents (model := model) width).map duration).sum +
        ((scaleBodyEvents (model := model) width).map duration).sum := by
  rcases path with ⟨⟨first, second, third⟩, ⟨fourth, fifth, sixth⟩⟩
  simp only [preparationScale, scalePairBody, scaleBody, Circuit.depth_seq,
    BitWord.bitWord_instruction_depth]
  simp [scaleBodyEvents, scaleProductOp, scaleDivisionOp, scaleQuotientOp, ClassicalOp.label]

private lemma final_duration_le (refs : PreparationRefs ctx width)
    (duration : Resource.Event model → Nat) (path : (preparationFinalize (model := model)
      refs).Path) :
    (preparationFinalize (model := model) refs).depth duration path ≤
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))) +
        (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width))) +
          max (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width))))
            (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width))))) := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · change (BitWord.instruction (execution := model)
          (negateSubtractOp (scaleRead refs.modulus) (scaleRead refs.right)
            refs.negatedRight)).Path at branchPath
        change (BitWord.instruction (execution := model) refs.narrowOp).depth duration resizePath +
          ((BitWord.instruction (execution := model)
            (negateEqualOp (scaleRead refs.right) (scaleRead refs.zero) refs.negationFlag)).depth
              duration testPath +
            (BitWord.instruction (execution := model)
              (negateSubtractOp (scaleRead refs.modulus) (scaleRead refs.right)
                refs.negatedRight)).depth duration branchPath) ≤ _
        rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
          BitWord.bitWord_instruction_depth]
        exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_max_right _ _) _) _
      · change (BitWord.instruction (execution := model)
          (negateCopyOp (scaleRead refs.zero) refs.negatedRight)).Path at branchPath
        change (BitWord.instruction (execution := model) refs.narrowOp).depth duration resizePath +
          ((BitWord.instruction (execution := model)
            (negateEqualOp (scaleRead refs.right) (scaleRead refs.zero) refs.negationFlag)).depth
              duration testPath +
            (BitWord.instruction (execution := model)
              (negateCopyOp (scaleRead refs.zero) refs.negatedRight)).depth
                duration branchPath) ≤ _
        rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
          BitWord.bitWord_instruction_depth]
        exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_max_left _ _) _) _

/-- Arbitrary native durations charge the full actual serial preparation. -/
lemma preparationBody_depth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (duration : Resource.Event model → Nat)
    (path : (preparationBody (model := model) spec input refs).Path) :
    (preparationBody (model := model) spec input refs).depth duration path ≤
      preparationDepthLimit spec duration := by
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (measuredDecodeInto_depth_le input refs.decoded duration path.1.1.1)
        (split_duration refs.split duration path.1.1.2).le)
      (Nat.add_le_add (ConstantWord.constantFold_depth (model := model) refs.modulusWide _
        duration path.1.2.1).le
        (seed_duration refs.denominator duration path.1.2.2).le))
    (Nat.add_le_add (scale_duration refs duration path.2.1).le
      (final_duration_le refs duration path.2.2))

private lemma seed_visited (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (scaleSeed (model := model) denominator).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (scaleSeed (model := model) denominator).visitedContexts path) :
      visited = ctx := by
  change visited ∈ [ctx] ++ (Word.PowerOfTwo.shiftInto (model := model) width
    denominator).visitedContexts path.2
    at present
  rcases List.mem_append.mp present with first | later
  · exact List.mem_singleton.mp first
  · exact Word.PowerOfTwo.shiftInto_visited width denominator path.2 visited later

private lemma scale_visited (refs : PreparationRefs ctx width)
    (path : (preparationScale (model := model) refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (preparationScale (model := model) refs).visitedContexts path) :
      visited = ctx := by
  change visited ∈ ([ctx] ++ ([ctx] ++ [ctx])) ++ ([ctx] ++ ([ctx] ++ [ctx])) at present
  simpa only [List.mem_append, List.mem_singleton, or_self] using present

private lemma final_visited (refs : PreparationRefs ctx width)
    (path : (preparationFinalize (model := model) refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (preparationFinalize (model := model) refs).visitedContexts path) :
      visited = ctx := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit <;>
        change visited ∈ [ctx] ++ ([ctx] ++ [ctx]) at present <;>
        simpa only [List.mem_append, List.mem_singleton, or_self] using present

private lemma preparation_visited (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody (model := model) spec input
      refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (preparationBody (model := model) spec input refs).visitedContexts path) :
    visited ∈ (measuredDecodeInto (model := model) input refs.decoded).visitedContexts path.1.1.1 ∨
      visited = ctx := by
  change visited ∈
    (((measuredDecodeInto (model := model) input refs.decoded).visitedContexts path.1.1.1 ++
      (Word.Split.splitInto (model := model) refs.split).visitedContexts path.1.1.2) ++
      ((ConstantWord.circuit (model := model) refs.modulusWide spec.modulus).visitedContexts
        path.1.2.1 ++
        (scaleSeed (model := model) refs.denominator).visitedContexts path.1.2.2)) ++
      ((preparationScale (model := model) refs).visitedContexts path.2.1 ++
        (preparationFinalize (model := model) refs).visitedContexts path.2.2) at present
  simp only [List.mem_append] at present
  rcases present with ((decode | split) | (loaded | seed)) | (scaled | final)
  · exact Or.inl decode
  · exact Or.inr (Word.Split.splitInto_visited refs.split path.1.1.2 visited split)
  · exact Or.inr (ConstantWord.constantWord_fold_visited refs.modulusWide _
      path.1.2.1 visited loaded)
  · exact Or.inr (seed_visited refs.denominator path.1.2.2 visited seed)
  · exact Or.inr (scale_visited refs path.2.1 visited scaled)
  · exact Or.inr (final_visited refs path.2.2 visited final)

/-- Only the actual finite-measurement decoder adds a cell inside the preparation body. -/
lemma preparationBody_resident_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody (model := model) spec input
      refs).Path) :
    (preparationBody (model := model) spec input refs).peakResidentSpace path ≤
      SpacePool.ofShape (.bits (width + width)) + ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases preparation_visited spec input refs path visited present with decoded | original
  · exact ((measuredDecodeInto (model := model) input refs.decoded).residentSpace_le_peak_of_visited
      path.1.1.1 visited decoded).trans
        (measuredDecodeInto_resident input refs.decoded path.1.1.1).le
  · exact original ▸ le_add_self

/-- The same actual decoder cell bounds auxiliary space beside all supplied preparation cells. -/
lemma preparationBody_auxiliary_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody (model := model) spec input
      refs).Path) :
    (preparationBody (model := model) spec input refs).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.bits (width + width)) + ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases preparation_visited spec input refs path visited present with decoded | original
  · exact ((measuredDecodeInto (model := model) input
    refs.decoded).auxiliarySpace_le_peak_of_visited
      path.1.1.1 visited decoded).trans
        (measuredDecodeInto_auxiliary input refs.decoded path.1.1.1).le
  · exact original ▸ le_add_self

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
