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

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Bounds

/-!
# Native nearest-preparation budgets and actual lexical space

Independent event and duration allowances charge the two seven-operation
nearest scalings. The one extra product-width word is retained in the actual
outer fourteen-cell allocation. Only the measured-bit decoder allocates
further scratch while the supplied preparation cells remain live.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalAlgorithms.Modular RawRecovery.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The unchanged original phases give an independent native preparation allowance. -/
def preparationEnvelope (model : ExecutionModel) [BitWord.Selected model] (spec : ModulusSpec
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
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationBody (model := model) spec input
      refs half).Path) :
    (preparationBody (model := model) spec input refs half).resourcePool path ≤ preparationEnvelope
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
  change ResourcePool.ofList ((preparationBody (model := model) spec input refs half).eventTrace
    path) ≤ _
  rw [preparationBody_eventTrace]
  simp only [ResourcePool.ofList_append]
  exact add_le_add
    (add_le_add (add_le_add (measuredDecodeInto_resourcePool_le input refs.decoded path.1.1.1)
      le_rfl) (add_le_add loaded.le le_rfl))
    (add_le_add le_rfl (add_le_add le_rfl selected))

/-- Independent duration bound retains all original serial dependencies and branch maxima. -/
def preparationDepthLimit (spec : ModulusSpec width)
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

private lemma scaleBody_duration (refs : ScaleRefs ctx width)
    (duration : Resource.Event model → Nat)
    (path : (scaleBody (model := model) refs).Path) :
    (scaleBody (model := model) refs).depth duration path =
      ((scaleBodyEvents (model := model) width).map duration).sum := by
  change (BitWord.instruction (execution := model)
    (scaleProductOp refs.raw refs.order refs.product)).depth duration path.1 +
    ((BitWord.instruction (execution := model) refs.halfResizeOp).depth duration path.2.1 +
      ((BitWord.instruction (execution := model) refs.halfShiftOp).depth duration path.2.2.1 +
        ((BitWord.instruction (execution := model) refs.roundOp).depth duration path.2.2.2.1 +
          ((BitWord.instruction (execution := model) refs.divideOp).depth duration path.2.2.2.2.1 +
            ((BitWord.instruction (execution := model) refs.reduceOp).depth duration
                path.2.2.2.2.2.1 +
              (BitWord.instruction (execution := model) refs.finishOp).depth duration
                path.2.2.2.2.2.2))))) = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_depth]
  simp [scaleBodyEvents, RawRecovery.Native.scaleProductOp,
    ScaleRefs.halfResizeOp, ScaleRefs.halfShiftOp, ScaleRefs.roundOp,
    ScaleRefs.divideOp, ScaleRefs.reduceOp, ScaleRefs.finishOp, ClassicalOp.label]

private lemma scale_duration (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (duration : Resource.Event model → Nat)
    (path : (preparationScale (model := model) refs half).Path) :
    (preparationScale (model := model) refs half).depth duration path =
      ((scaleBodyEvents (model := model) width).map duration).sum +
        ((scaleBodyEvents (model := model) width).map duration).sum := by
  exact congrArg₂ (· + ·)
    (scaleBody_duration (scaleRefs refs half false) duration path.1)
    (scaleBody_duration (scaleRefs refs half true) duration path.2)

/-- Arbitrary native durations charge the full actual serial preparation. -/
lemma preparationBody_depth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (duration : Resource.Event model → Nat)
    (path : (preparationBody (model := model) spec input refs half).Path) :
    (preparationBody (model := model) spec input refs half).depth duration path ≤
      preparationDepthLimit spec duration := by
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (measuredDecodeInto_depth_le input refs.decoded duration path.1.1.1)
        (split_duration refs.split duration path.1.1.2).le)
      (Nat.add_le_add (ConstantWord.constantFold_depth (model := model) refs.modulusWide _
        duration path.1.2.1).le
        (seed_duration refs.denominator duration path.1.2.2).le))
    (Nat.add_le_add (scale_duration refs half duration path.2.1).le
      (final_duration_le refs duration path.2.2))

private lemma scale_visited (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationScale (model := model) refs half).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (preparationScale (model := model) refs half).visitedContexts path) :
      visited = ctx := by
  change visited ∈
    ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])))))) ++
      ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])))))) at present
  simpa only [List.mem_append, List.mem_singleton, or_self] using present

private lemma preparation_visited (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationBody (model := model) spec input
      refs half).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈
      (preparationBody (model := model) spec input refs half).visitedContexts path) :
    visited ∈ (measuredDecodeInto (model := model) input refs.decoded).visitedContexts path.1.1.1 ∨
      visited = ctx := by
  change visited ∈
    (((measuredDecodeInto (model := model) input refs.decoded).visitedContexts path.1.1.1 ++
      (Word.Split.splitInto (model := model) refs.split).visitedContexts path.1.1.2) ++
      ((ConstantWord.circuit (model := model) refs.modulusWide spec.modulus).visitedContexts
        path.1.2.1 ++
        (scaleSeed (model := model) refs.denominator).visitedContexts path.1.2.2)) ++
      ((preparationScale (model := model) refs half).visitedContexts path.2.1 ++
        (preparationFinalize (model := model) refs).visitedContexts path.2.2) at present
  simp only [List.mem_append] at present
  rcases present with ((decode | split) | (loaded | seed)) | (scaled | final)
  · exact Or.inl decode
  · exact Or.inr (Word.Split.splitInto_visited refs.split path.1.1.2 visited split)
  · exact Or.inr (ConstantWord.constantWord_fold_visited refs.modulusWide _
      path.1.2.1 visited loaded)
  · exact Or.inr (seed_visited refs.denominator path.1.2.2 visited seed)
  · exact Or.inr (scale_visited refs half path.2.1 visited scaled)
  · exact Or.inr (final_visited refs path.2.2 visited final)

/-- Only the actual finite-measurement decoder adds a cell inside the preparation body. -/
lemma preparationBody_resident_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationBody (model := model) spec input
      refs half).Path) :
    (preparationBody (model := model) spec input refs half).peakResidentSpace path ≤
      SpacePool.ofShape (.bits (width + width)) + ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases preparation_visited spec input refs half path visited present with decoded | original
  · exact ((measuredDecodeInto (model := model) input refs.decoded).residentSpace_le_peak_of_visited
      path.1.1.1 visited decoded).trans
        (measuredDecodeInto_resident input refs.decoded path.1.1.1).le
  · exact original ▸ le_add_self

/-- The same actual decoder cell bounds auxiliary space beside all supplied preparation cells. -/
lemma preparationBody_auxiliary_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationBody (model := model) spec input
      refs half).Path) :
    (preparationBody (model := model) spec input refs half).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.bits (width + width)) + ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases preparation_visited spec input refs half path visited present with decoded | original
  · exact ((measuredDecodeInto (model := model) input
    refs.decoded).auxiliarySpace_le_peak_of_visited
      path.1.1.1 visited decoded).trans
        (measuredDecodeInto_auxiliary input refs.decoded path.1.1.1).le
  · exact original ▸ le_add_self

/-- The actual preparation allocator charges the extra full-product-width half word. -/
lemma preparationSpace_eq (kind : ProblemKind) (width : Nat) :
    ((preparationShapes width).map (SpacePool.ofShape (kind := kind))).sum =
      SpacePool.ofShape (.unsignedWord (width + (width + 1))) +
        ((RawRecovery.Native.preparationShapes width).map SpacePool.ofShape).sum := rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
