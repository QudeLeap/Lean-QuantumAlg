/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Trace

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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original independent selected-negation allowance after the modulus resize. -/
def preparationFinalEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList [.classicalOperation (.wordResize (width + 1) width)] +
    ResourcePool.max (ResourcePool.ofList (negateEvents kind width true))
      (ResourcePool.ofList (negateEvents kind width false))

/-- The unchanged original phases give an independent native preparation allowance. -/
def preparationEnvelope (kind : ProblemKind) (spec : ModulusSpec width) : ResourcePool kind :=
  ((measuredDecodeEnvelope (width + width) +
    ResourcePool.ofList (Word.Split.splitTrace width width)) +
    (ResourcePool.ofList (ConstantWord.loaderTrace kind (width + 1)
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))) +
        ResourcePool.ofList (preparationSeedEvents kind width))) +
    ((ResourcePool.ofList (scaleBodyEvents kind width) +
      ResourcePool.ofList (scaleBodyEvents kind width)) + preparationFinalEnvelope kind width)

/-- Each actual original preparation path fits the independent phase allowances. -/
theorem preparationBody_pool_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody spec input refs).Path) :
    (preparationBody spec input refs).resourcePool path ≤ preparationEnvelope kind spec := by
  have loaded := congrArg ResourcePool.ofList (ConstantWord.constantFold_eventTrace refs.modulusWide
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.1.2.1)
  have selected : ResourcePool.ofList (negateEvents kind width path.2.2.2.2.1.toBool) ≤
      ResourcePool.max (ResourcePool.ofList (negateEvents kind width true))
        (ResourcePool.ofList (negateEvents kind width false)) := by
    cases path.2.2.2.2.1.toBool
    · exact ResourcePool.le_max_right _ _
    · exact ResourcePool.le_max_left _ _
  change ResourcePool.ofList ((preparationBody spec input refs).eventTrace path) ≤ _
  rw [preparationBody_eventTrace]
  simp only [ResourcePool.ofList_append]
  exact add_le_add
    (add_le_add (add_le_add (measuredDecodeInto_resourcePool_le input refs.decoded path.1.1.1)
      le_rfl) (add_le_add loaded.le le_rfl))
    (add_le_add le_rfl (add_le_add le_rfl selected))

/-- Independent duration bound retains all original serial dependencies and branch maxima. -/
def preparationDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event kind → Nat) : Nat :=
  ((duration (measuredPackEvent (width + width)) + (width + width) *
      (duration (TerminalDecode.shiftEvent (width + width)) +
        duration (TerminalDecode.incrementEvent (width + width))) +
      (((Word.Split.splitTrace width width).map duration).sum)) +
    (((ConstantWord.loaderTrace kind (width + 1)
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))).map duration).sum +
        ((preparationSeedEvents kind width).map duration).sum)) +
    ((((scaleBodyEvents kind width).map duration).sum +
      ((scaleBodyEvents kind width).map duration).sum) +
      (duration (.classicalOperation (.wordResize (width + 1) width)) +
        (duration (.classicalOperation (.wordBinary .equal width)) +
          max (duration (.classicalOperation (.wordUnary .copy width)))
            (duration (.classicalOperation (.wordBinary .sub width))))))

private theorem split_duration (refs : Word.Split.Refs ctx width width)
    (duration : Resource.Event kind → Nat) (path : (Word.Split.splitInto refs).Path) :
    (Word.Split.splitInto refs).depth duration path =
      ((Word.Split.splitTrace width width).map duration).sum := by
  change duration (.classicalOperation (.wordResize (width + width) width)) +
    ((0 + ∑ _index : Fin width,
      duration (.classicalOperation (.wordUnary .shiftRight (width + width)))) +
      duration (.classicalOperation (.wordResize (width + width) width))) = _
  simp [Word.Split.splitTrace, Word.Split.shiftTrace]

private theorem seed_duration (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event kind → Nat) (path : (scaleSeed denominator).Path) :
    (scaleSeed denominator).depth duration path =
      ((preparationSeedEvents kind width).map duration).sum := by
  change duration (.classicalOperation (.wordUnary .increment (width + 1))) +
    (0 + ∑ _index : Fin width,
      duration (.classicalOperation (.wordUnary .shiftLeft (width + 1)))) = _
  simp [preparationSeedEvents, Word.PowerOfTwo.shiftTrace]

private theorem scale_duration (refs : PreparationRefs ctx width)
    (duration : Resource.Event kind → Nat) (path : (preparationScale refs).Path) :
    (preparationScale refs).depth duration path =
      ((scaleBodyEvents kind width).map duration).sum +
        ((scaleBodyEvents kind width).map duration).sum := by
  simp only [scaleBodyEvents, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  rfl

private theorem final_duration_le (refs : PreparationRefs ctx width)
    (duration : Resource.Event kind → Nat) (path : (preparationFinalize refs).Path) :
    (preparationFinalize refs).depth duration path ≤
      duration (.classicalOperation (.wordResize (width + 1) width)) +
        (duration (.classicalOperation (.wordBinary .equal width)) +
          max (duration (.classicalOperation (.wordUnary .copy width)))
            (duration (.classicalOperation (.wordBinary .sub width)))) := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_max_right _ _) _) _
      · exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_max_left _ _) _) _

/-- Arbitrary native durations charge the full actual serial preparation. -/
theorem preparationBody_depth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (duration : Resource.Event kind → Nat)
    (path : (preparationBody spec input refs).Path) :
    (preparationBody spec input refs).depth duration path ≤
      preparationDepthLimit spec duration := by
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (measuredDecodeInto_depth_le input refs.decoded duration path.1.1.1)
        (split_duration refs.split duration path.1.1.2).le)
      (Nat.add_le_add (ConstantWord.constantFold_depth refs.modulusWide _ duration path.1.2.1).le
        (seed_duration refs.denominator duration path.1.2.2).le))
    (Nat.add_le_add (scale_duration refs duration path.2.1).le
      (final_duration_le refs duration path.2.2))

private theorem seed_visited (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (scaleSeed denominator).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (scaleSeed denominator).visitedContexts path) : visited = ctx := by
  change visited ∈ [ctx] ++ (Word.PowerOfTwo.shiftInto width denominator).visitedContexts path.2
    at present
  rcases List.mem_append.mp present with first | later
  · exact List.mem_singleton.mp first
  · exact Word.PowerOfTwo.shiftInto_visited width denominator path.2 visited later

private theorem scale_visited (refs : PreparationRefs ctx width)
    (path : (preparationScale refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (preparationScale refs).visitedContexts path) : visited = ctx := by
  change visited ∈ ([ctx] ++ ([ctx] ++ [ctx])) ++ ([ctx] ++ ([ctx] ++ [ctx])) at present
  simpa only [List.mem_append, List.mem_singleton, or_self] using present

private theorem final_visited (refs : PreparationRefs ctx width)
    (path : (preparationFinalize refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (preparationFinalize refs).visitedContexts path) : visited = ctx := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit <;>
        change visited ∈ [ctx] ++ ([ctx] ++ [ctx]) at present <;>
        simpa only [List.mem_append, List.mem_singleton, or_self] using present

private theorem preparation_visited (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody spec input refs).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈ (preparationBody spec input refs).visitedContexts path) :
    visited ∈ (measuredDecodeInto input refs.decoded).visitedContexts path.1.1.1 ∨
      visited = ctx := by
  change visited ∈
    (((measuredDecodeInto input refs.decoded).visitedContexts path.1.1.1 ++
      (Word.Split.splitInto refs.split).visitedContexts path.1.1.2) ++
      ((ConstantWord.circuit refs.modulusWide spec.modulus).visitedContexts path.1.2.1 ++
        (scaleSeed refs.denominator).visitedContexts path.1.2.2)) ++
      ((preparationScale refs).visitedContexts path.2.1 ++
        (preparationFinalize refs).visitedContexts path.2.2) at present
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
theorem preparationBody_resident_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody spec input refs).Path) :
    (preparationBody spec input refs).peakResidentSpace path ≤
      SpacePool.ofShape (.bits (width + width)) + ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases preparation_visited spec input refs path visited present with decoded | original
  · exact ((measuredDecodeInto input refs.decoded).residentSpace_le_peak_of_visited
      path.1.1.1 visited decoded).trans
        (measuredDecodeInto_resident input refs.decoded path.1.1.1).le
  · exact original ▸ le_add_self

/-- The same actual decoder cell bounds auxiliary space beside all supplied preparation cells. -/
theorem preparationBody_auxiliary_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody spec input refs).Path) :
    (preparationBody spec input refs).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.bits (width + width)) + ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases preparation_visited spec input refs path visited present with decoded | original
  · exact ((measuredDecodeInto input refs.decoded).auxiliarySpace_le_peak_of_visited
      path.1.1.1 visited decoded).trans
        (measuredDecodeInto_auxiliary input refs.decoded path.1.1.1).le
  · exact original ▸ le_add_self

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
