/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation.Bounds
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources

/-!
# Paid nearest raw exposure budgets

The complete actual fourteen-cell allocation encloses the nearest preparation
and unchanged checked inverse and three-cell exposure. The extra half word
and all eight additional rounding and wrap operations occur in this budget.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular RawRecovery.Native
open NumberTheory.Checked.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent nearest preparation and actual checked-exposure native allowances. -/
def singleExposureEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : ResourcePool model :=
  preparationEnvelope model spec + checkedExposureEnvelope model spec

/-- Actual nearest preparation and checked exposure retain their serial dependencies. -/
def singleExposureDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event model → Nat) : Nat :=
  preparationDepthLimit spec duration + checkedExposureDepthLimit spec duration

/-- The complete actual raw exposure retains every stage and scope in its pool bound. -/
lemma singleIntoCells_pool_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).Path) :
    (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).resourcePool path ≤
      singleExposureEnvelope model spec := by
  exact withCellsFrom_pool_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref)
      (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (singleExposureEnvelope model spec) (by
      intro inner cells distinct transport separated selected
      change ResourcePool.ofList
        ((preparationBody (model := model) spec (transport.liftInput input) (preparationRefs
          cells.tail) cells.head.ref).eventTrace
          selected.1 ++
          (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
            (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
            (transport.liftWrite reconstruction)).eventTrace selected.2) ≤ _
      rw [ResourcePool.ofList_append]
      exact add_le_add (preparationBody_pool_le _ _ _ _ selected.1)
        (withCheckedExposure_pool_le _ _ _ _ _ selected.2)) path

/-- The complete actual raw exposure retains every stage and scope in its depth bound. -/
lemma singleIntoCells_depth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).Path) :
    (singleIntoCells (model := model) spec input inverseSuccess candidate reconstruction).depth
      duration path ≤
      singleExposureDepthLimit spec duration := by
  exact withCellsFrom_depth_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref)
      (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    duration (singleExposureDepthLimit spec duration) (by
      intro inner cells distinct transport separated selected
      exact Nat.add_le_add (preparationBody_depth_le _ _ _ _ duration selected.1)
        (withCheckedExposure_depth_le _ _ _ _ _ duration selected.2)) path

/-- The complete actual raw exposure retains every stage and scope in its resident bound. -/
lemma singleIntoCells_resident_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).Path) :
    (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).peakResidentSpace path ≤
      ((preparationShapes width).map SpacePool.ofShape).sum +
        singleExposureActiveSpace model.kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref)
      (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (singleExposureActiveSpace model.kind width) (by
      intro inner cells distinct transport separated selected
      refine (Circuit.peakResidentSpace_seq _ _ selected).le.trans (SpacePool.max_le ?_ ?_)
      · exact (preparationBody_resident_le _ _ _ _ selected.1).trans
          (add_le_add (SpacePool.le_max_left _ _) le_rfl)
      · exact (withCheckedExposure_resident_le _ _ _ _ _ selected.2).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)) path

/-- The complete actual raw exposure retains every stage and scope in its auxiliary bound. -/
lemma singleIntoCells_auxiliary_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).Path) :
    (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).peakAuxiliarySpace path ≤
      ((preparationShapes width).map SpacePool.ofShape).sum +
        singleExposureActiveSpace model.kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref)
      (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (singleExposureActiveSpace model.kind width) (by
      intro inner cells distinct transport separated selected
      refine (Circuit.peakAuxiliarySpace_seq _ _ selected).le.trans (SpacePool.max_le ?_ ?_)
      · exact (preparationBody_auxiliary_le _ _ _ _ selected.1).trans
          (add_le_add (SpacePool.le_max_left _ _) le_rfl)
      · exact (withCheckedExposure_auxiliary_le _ _ _ _ _ selected.2).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)) path

/-- Unit durations charge preparation and eleven possible recovery and copy instructions. -/
lemma singleIntoCells_unitDepth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).Path) :
    (singleIntoCells (model := model) spec input inverseSuccess candidate reconstruction).depth
      (fun _ => 1) path ≤
      8 * width + 34 + checkedInverseDepthLimit (model := model) spec (fun _ => 1) := by
  exact withCellsFrom_depth_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref)
      (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (fun _ => 1) (8 * width + 34 + checkedInverseDepthLimit (model := model) spec (fun _ => 1)) (by
      intro inner cells distinct transport separated selected
      have prepared := preparationBody_unitDepth_le spec
        (transport.liftInput input) (preparationRefs cells.tail) cells.head.ref selected.1
      have later := withCheckedExposure_depth_le spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction) (fun _ => 1) selected.2
      change (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)).depth (fun _ => 1) selected.2 ≤
          checkedInverseDepthLimit (model := model) spec (fun _ => 1) + 11 at later
      change (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs
        cells.tail) cells.head.ref).depth
        (fun _ => 1) selected.1 +
        (withCheckedExposure (model := model) spec (preparationRefs cells.tail)
          (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
          (transport.liftWrite reconstruction)).depth (fun _ => 1) selected.2 ≤ _
      omega) path

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
