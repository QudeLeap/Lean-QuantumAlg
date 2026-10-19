/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.CheckedSelection.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Bounds

/-!
# Actual complete single-sample Fourier recovery resources

The original thirteen preparation cells remain live through checked and
selected recovery. The temporary finite-bit decoder ends before the two
checked output cells are allocated. Independent native and duration bounds
follow the same actual program, including both original modulus loaders,
the single shared denominator seed and final optional-result materialization.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open NumberTheory.Checked.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent original preparation, checked inverse and selected recovery allowances. -/
def singleRecoveryEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : ResourcePool model :=
  preparationEnvelope model spec + checkedRecoveryEnvelope model spec

/-- The three original phases retain their chronological native-duration dependencies. -/
def singleRecoveryDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event model → Nat) : Nat :=
  preparationDepthLimit spec duration + checkedRecoveryDepthLimit spec duration

/-- Decoder bits are released before checked results and later arithmetic workspaces are live. -/
def singleRecoveryActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (.bits (width + width)))
    (((checkedResultShapes width).map SpacePool.ofShape).sum +
      checkedRecoveryActiveSpace kind width)

/-- All actual single-sample native events fit the original independent arithmetic allowance. -/
lemma singleIntoResult_pool_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width))
    (path : (singleIntoResult (model := model) spec input result).Path) :
    (singleIntoResult (model := model) spec input result).resourcePool path ≤
      singleRecoveryEnvelope model spec := by
  exact withCellsFrom_pool_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedSelection (model := model) spec (preparationRefs cells) (transport.liftWrite
        result)))
    (singleRecoveryEnvelope model spec) (by
      intro inner cells distinct transport separated selected
      change ResourcePool.ofList
        ((preparationBody (model := model) spec (transport.liftInput input) (preparationRefs
          cells)).eventTrace
          selected.1 ++
          (withCheckedSelection (model := model) spec (preparationRefs cells)
            (transport.liftWrite result)).eventTrace
            selected.2) ≤ _
      rw [ResourcePool.ofList_append]
      exact add_le_add (preparationBody_pool_le _ _ _ selected.1)
        (withCheckedSelection_pool_le _ _ _ selected.2)) path

/-- The actual full recovery sequence satisfies the original serial duration bound. -/
lemma singleIntoResult_depth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width)) (duration : Resource.Event model → Nat)
    (path : (singleIntoResult (model := model) spec input result).Path) :
    (singleIntoResult (model := model) spec input result).depth duration path ≤
      singleRecoveryDepthLimit spec duration := by
  exact withCellsFrom_depth_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedSelection (model := model) spec (preparationRefs cells) (transport.liftWrite
        result)))
    duration (singleRecoveryDepthLimit spec duration) (by
      intro inner cells distinct transport separated selected
      exact Nat.add_le_add (preparationBody_depth_le _ _ _ duration selected.1)
        (withCheckedSelection_depth_le _ _ _ duration selected.2)) path

/-- Unit durations charge the full original preparation and nine possible recovery instructions. -/
lemma singleIntoResult_unitDepth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width))
    (path : (singleIntoResult (model := model) spec input result).Path) :
    (singleIntoResult (model := model) spec input result).depth (fun _ => 1) path ≤
      8 * width + 24 + checkedInverseDepthLimit (model := model) spec (fun _ => 1) := by
  exact withCellsFrom_depth_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedSelection (model := model) spec (preparationRefs cells) (transport.liftWrite
        result)))
    (fun _ => 1) (8 * width + 24 + checkedInverseDepthLimit (model := model) spec (fun _ => 1)) (by
      intro inner cells distinct transport separated selected
      have prepared := preparationBody_unitDepth_le spec
        (transport.liftInput input) (preparationRefs cells) selected.1
      have later := withCheckedSelection_depth_le spec (preparationRefs cells)
        (transport.liftWrite result) (fun _ => 1) selected.2
      change (withCheckedSelection (model := model) spec (preparationRefs cells)
        (transport.liftWrite result)).depth (fun _ => 1) selected.2 ≤
          checkedInverseDepthLimit (model := model) spec (fun _ => 1) + 9 at later
      change (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs
        cells)).depth
        (fun _ => 1) selected.1 +
        (withCheckedSelection (model := model) spec (preparationRefs cells) (transport.liftWrite
          result)).depth
          (fun _ => 1) selected.2 ≤ _
      omega) path

/-- Thirteen real preparation cells coexist with the larger successive active-scope allowance. -/
lemma singleIntoResult_resident_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width))
    (path : (singleIntoResult (model := model) spec input result).Path) :
    (singleIntoResult (model := model) spec input result).peakResidentSpace path ≤
      ((preparationShapes width).map SpacePool.ofShape).sum +
        singleRecoveryActiveSpace model.kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedSelection (model := model) spec (preparationRefs cells) (transport.liftWrite
        result)))
    (singleRecoveryActiveSpace model.kind width) (by
      intro inner cells distinct transport separated selected
      refine (Circuit.peakResidentSpace_seq _ _ selected).le.trans (SpacePool.max_le ?_ ?_)
      · exact (preparationBody_resident_le _ _ _ selected.1).trans
          (add_le_add (SpacePool.le_max_left _ _) le_rfl)
      · exact (withCheckedSelection_resident_le _ _ _ selected.2).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)) path

/-- Actual auxiliary ownership includes every original caller and retained preparation scope. -/
lemma singleIntoResult_auxiliary_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width))
    (path : (singleIntoResult (model := model) spec input result).Path) :
    (singleIntoResult (model := model) spec input result).peakAuxiliarySpace path ≤
      ((preparationShapes width).map SpacePool.ofShape).sum +
        singleRecoveryActiveSpace model.kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedSelection (model := model) spec (preparationRefs cells) (transport.liftWrite
        result)))
    (singleRecoveryActiveSpace model.kind width) (by
      intro inner cells distinct transport separated selected
      refine (Circuit.peakAuxiliarySpace_seq _ _ selected).le.trans (SpacePool.max_le ?_ ?_)
      · exact (preparationBody_auxiliary_le _ _ _ selected.1).trans
          (add_le_add (SpacePool.le_max_left _ _) le_rfl)
      · exact (withCheckedSelection_auxiliary_le _ _ _ selected.2).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)) path

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
