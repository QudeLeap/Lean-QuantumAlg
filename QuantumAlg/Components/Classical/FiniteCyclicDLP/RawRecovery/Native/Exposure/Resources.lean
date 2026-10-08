/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
public import
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.CheckedSelection.Resources
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Bounds
public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Core.Base.Accounting.Event
public import QuantumAlg.Core.Base.Accounting.Kind
public import QuantumAlg.Core.Base.Accounting.Space
public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Util.Classical.Modular.Basic
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.CheckedSelection.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Bounds
import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Model
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Actual three-cell recovery exposure resources

The selected successful recovery performs its eight original operations,
including product materialization, before the three original output copies.
Failure performs only those three copies. Preparation, actual checked inversion,
the thirteen preparation cells, two checked outputs and selected payload are
all charged with their actual lexical lifetimes and the complete caller context.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open NumberTheory.Checked.Native NormalizedRecovery.Native Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original three chronological caller-output copies. -/
def exposureCopyEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .copy)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .copy))]

/-- Only the actual successful branch incurs the original normalized recovery. -/
def selectedExposureEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat)
  (selected : Bool) :
    List (Resource.Event model) :=
  (if selected then recoveryEvents model width else []) ++ exposureCopyEvents model width

private theorem exposureCopy_eventTrace
    (success : CInputRef ctx .bit) (recoveredCandidate : CInputRef ctx (.unsignedWord width))
    (verified : CInputRef ctx .bit) (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width)) (reconstruction : CWriteRef ctx .bit)
    (path : (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).Path) :
    (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).eventTrace path =
        exposureCopyEvents model width := by
  change (BitWord.instruction (execution := model)
    (.bit .copy ctx success inverseSuccess)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model)
        (.wordUnary .copy width ctx recoveredCandidate candidate)).eventTrace path.2.1 ++
          (BitWord.instruction (execution := model)
            (.bit .copy ctx verified reconstruction)).eventTrace path.2.2) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private theorem exposureCopy_duration
    (success : CInputRef ctx .bit) (recoveredCandidate : CInputRef ctx (.unsignedWord width))
    (verified : CInputRef ctx .bit) (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width)) (reconstruction : CWriteRef ctx .bit)
      (duration : Resource.Event model → Nat)
    (path : (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).Path) :
    (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).depth duration path =
        ((exposureCopyEvents model width).map duration).sum := by
  change (BitWord.instruction (execution := model)
    (.bit .copy ctx success inverseSuccess)).depth duration path.1 +
      ((BitWord.instruction (execution := model)
        (.wordUnary .copy width ctx recoveredCandidate candidate)).depth duration path.2.1 +
          (BitWord.instruction (execution := model)
            (.bit .copy ctx verified reconstruction)).depth duration path.2.2) = _
  simp only [BitWord.bitWord_instruction_depth]
  rfl

/-- Actual status-selected recovery has its eight operations followed by the three copies. -/
theorem withSelectedExposure_eventTrace
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    (withSelectedExposure (model := model) input modulus success inverseSuccess candidate
      reconstruction).eventTrace
      path = selectedExposureEvents model width path.1.1.toBool := by
  rcases path with ⟨⟨value, chosen⟩, copied⟩
  cases value with
  | bit value =>
      cases value
      · change [] ++ (exposureCopyBody (model := model) (underSelection success width)
          (.first (scaleRead (selectionPayloadCell ctx width)))
          (.second (scaleRead (selectionPayloadCell ctx width)))
          (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
          (writeUnderSelection reconstruction width)).eventTrace copied = _
        rw [exposureCopy_eventTrace]
        rfl
      · change (withRecovery (model := model) (underSelection input width)
          (underSelection modulus width) (selectionPayloadCell ctx width)).Path at chosen
        change (withRecovery (model := model) (underSelection input width)
          (underSelection modulus width) (selectionPayloadCell ctx width)).eventTrace chosen ++
          (exposureCopyBody (model := model) (underSelection success width)
          (.first (scaleRead (selectionPayloadCell ctx width)))
          (.second (scaleRead (selectionPayloadCell ctx width)))
          (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
          (writeUnderSelection reconstruction width)).eventTrace copied = _
        rw [withRecovery_eventTrace, exposureCopy_eventTrace]
        rfl

/-- The stored success branch emits eleven events, and the failed branch emits three. -/
theorem withSelectedExposure_eventCount
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    ((withSelectedExposure (model := model) input modulus success inverseSuccess candidate
      reconstruction).eventTrace
      path).length = if path.1.1.toBool then 11 else 3 := by
  rw [withSelectedExposure_eventTrace]
  cases path.1.1.toBool <;> rfl

/-- Independent serial duration of successful normalized recovery and all three output copies. -/
def selectedExposureDepthLimit (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  (2 * multiplyDepth width duration +
    duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
      .equal width))) +
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.nominalEncoding (.packProduct width 1))))) +
        ((exposureCopyEvents model width).map duration).sum

/-- Actual durations retain the selected arithmetic and the common output-copy sequence. -/
theorem withSelectedExposure_durationDepth
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    (withSelectedExposure (model := model) input modulus success inverseSuccess candidate
      reconstruction).depth
      duration path =
        (if path.1.1.toBool then 2 * multiplyDepth width duration +
          duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordBinary .equal width))) +
            duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
              (.nominalEncoding (.packProduct width 1)))) else 0) +
              ((exposureCopyEvents model width).map duration).sum := by
  rcases path with ⟨⟨value, chosen⟩, copied⟩
  cases value with
  | bit value =>
      cases value
      · change 0 + (exposureCopyBody (model := model) (underSelection success width)
          (.first (scaleRead (selectionPayloadCell ctx width)))
          (.second (scaleRead (selectionPayloadCell ctx width)))
          (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
          (writeUnderSelection reconstruction width)).depth duration copied = _
        rw [exposureCopy_duration]
        rfl
      · change (withRecovery (model := model) (underSelection input width)
          (underSelection modulus width) (selectionPayloadCell ctx width)).Path at chosen
        change (withRecovery (model := model) (underSelection input width)
          (underSelection modulus width) (selectionPayloadCell ctx width)).depth duration chosen +
          (exposureCopyBody (model := model) (underSelection success width)
          (.first (scaleRead (selectionPayloadCell ctx width)))
          (.second (scaleRead (selectionPayloadCell ctx width)))
          (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
          (writeUnderSelection reconstruction width)).depth duration copied = _
        rw [withRecovery_durationDepth, exposureCopy_duration]
        rfl

private theorem selectedExposure_pool_le
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).resourcePool path ≤
        ResourcePool.ofList (selectedExposureEvents model width true) := by
  rw [Circuit.resourcePool, withSelectedExposure_eventTrace]
  cases selected : path.1.1.toBool
  · simp only [selectedExposureEvents, Bool.false_eq_true, if_false, if_true, List.nil_append]
    rw [ResourcePool.ofList_append]
    exact le_add_self
  · exact le_rfl

private theorem selectedExposure_depth_le
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    (withSelectedExposure (model := model) input modulus success inverseSuccess candidate
      reconstruction).depth
      duration path ≤ selectedExposureDepthLimit width duration := by
  rw [withSelectedExposure_durationDepth]
  cases selected : path.1.1.toBool
  · simp only [selectedExposureDepthLimit, Bool.false_eq_true, if_false, Nat.zero_add]
    omega
  · exact le_rfl

private theorem exposureCopy_resident
    (success : CInputRef ctx .bit) (recoveredCandidate : CInputRef ctx (.unsignedWord width))
    (verified : CInputRef ctx .bit) (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width)) (reconstruction : CWriteRef ctx .bit)
    (path : (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).Path) :
    (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).peakResidentSpace path = ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0)) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

private theorem exposureBody_resident_le
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (exposureBody (model := model) input modulus success payload
      inverseSuccess candidate reconstruction).Path) :
    (exposureBody (model := model) input modulus success payload
      inverseSuccess candidate reconstruction).peakResidentSpace path ≤
        recoveryScratchSpace width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rcases path.1 with ⟨value, chosen⟩
    cases value with
    | bit value =>
        cases value
        · change SpacePool.max ctx.residentSpace 0 ≤ _
          rw [SpacePool.max_zero]
          exact le_add_self
        · exact (withRecovery_resident input modulus payload chosen).le
  · exact (exposureCopy_resident _ _ _ _ _ _ path.2).le.trans le_add_self

/-- The real payload and successful recovery scratch bound every resident exposure path. -/
theorem withSelectedExposure_resident_le
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).peakResidentSpace path ≤
        selectedRecoveryScratchSpace width true + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh _ path).le.trans
      (SpacePool.max_le ?_ ?_)
  · exact le_add_self
  · simpa only [selectedRecoveryScratchSpace, if_true,
      RuntimeCtx.residentSpace_addWorkspace, add_assoc] using
        exposureBody_resident_le (underSelection input width) (underSelection modulus width)
          (underSelection success width) (selectionPayloadCell ctx width)
          (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
          (writeUnderSelection reconstruction width) path

private theorem exposureCopy_auxiliary
    (success : CInputRef ctx .bit) (recoveredCandidate : CInputRef ctx (.unsignedWord width))
    (verified : CInputRef ctx .bit) (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width)) (reconstruction : CWriteRef ctx .bit)
    (path : (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).Path) :
    (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0)) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

private theorem exposureBody_auxiliary_le
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (exposureBody (model := model) input modulus success payload
      inverseSuccess candidate reconstruction).Path) :
    (exposureBody (model := model) input modulus success payload
      inverseSuccess candidate reconstruction).peakAuxiliarySpace path ≤
        recoveryScratchSpace width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rcases path.1 with ⟨value, chosen⟩
    cases value with
    | bit value =>
        cases value
        · change SpacePool.max ctx.auxiliarySpace 0 ≤ _
          rw [SpacePool.max_zero]
          exact le_add_self
        · exact (withRecovery_auxiliary input modulus payload chosen).le
  · exact (exposureCopy_auxiliary _ _ _ _ _ _ path.2).le.trans le_add_self

/-- The real payload and successful recovery scratch bound every auxiliary exposure path. -/
theorem withSelectedExposure_auxiliary_le
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).Path) :
    (withSelectedExposure (model := model) input modulus success
      inverseSuccess candidate reconstruction).peakAuxiliarySpace path ≤
        selectedRecoveryScratchSpace width true + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh _ path).le.trans
      (SpacePool.max_le ?_ ?_)
  · exact le_add_self
  · simpa only [selectedRecoveryScratchSpace, if_true,
      RuntimeCtx.auxiliarySpace_addWorkspace, add_assoc] using
        exposureBody_auxiliary_le (underSelection input width) (underSelection modulus width)
          (underSelection success width) (selectionPayloadCell ctx width)
          (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
          (writeUnderSelection reconstruction width) path

/-- Checked inversion and the successful recovery-plus-copy allowance, with no optional pack. -/
public def checkedExposureEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec
  width) : ResourcePool model :=
  checkedInverseEnvelope model spec + ResourcePool.ofList (selectedExposureEvents model width true)

/-- Checked inversion is serially followed by the selected exposure. -/
public def checkedExposureDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event model → Nat) : Nat :=
  checkedInverseDepthLimit spec duration + selectedExposureDepthLimit width duration

private theorem checkedExposureBody_pool_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).Path) :
    (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).resourcePool path ≤
      checkedExposureEnvelope model spec := by
  change ResourcePool.ofList ((withCheckedInverse (model := model) spec left success
    inverse).eventTrace path.1 ++
    (withSelectedExposure (model := model) (.product left (.product negatedRight (scaleRead
      inverse))) modulus
      (scaleRead success) inverseSuccess candidate reconstruction).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (withCheckedInverse_pool_le spec left success inverse path.1)
    (selectedExposure_pool_le _ _ _ _ _ _ path.2)

/-- Both actual checked result cells remain live through the complete pool exposure bound. -/
theorem withCheckedExposure_pool_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).Path) :
    (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).resourcePool path ≤
      checkedExposureEnvelope model spec := by
  exact withCellsFrom_pool_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedExposureBody (model := model) spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells)
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction))
    (checkedExposureEnvelope model spec)
    (fun cells _ transport _ selected =>
      checkedExposureBody_pool_le _ _ _ _ _ _ _ _ _ selected) path

private theorem checkedExposureBody_depth_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).Path) :
    (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).depth duration path ≤
      checkedExposureDepthLimit spec duration := by
  exact Nat.add_le_add (withCheckedInverse_depth_le spec left success inverse duration path.1)
    (selectedExposure_depth_le _ _ _ _ _ _ duration path.2)

/-- Both actual checked result cells remain live through the complete depth exposure bound. -/
theorem withCheckedExposure_depth_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).Path) :
    (withCheckedExposure (model := model) spec refs inverseSuccess candidate reconstruction).depth
      duration path ≤
      checkedExposureDepthLimit spec duration := by
  exact withCellsFrom_depth_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedExposureBody (model := model) spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells)
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction))
    duration (checkedExposureDepthLimit spec duration)
    (fun cells _ transport _ selected =>
      checkedExposureBody_depth_le _ _ _ _ _ _ _ _ _ duration selected) path

private theorem checkedExposureBody_resident_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).Path) :
    (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).peakResidentSpace path ≤
      checkedRecoveryActiveSpace model.kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (withCheckedInverse_resident_le spec left success inverse path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (withSelectedExposure_resident_le _ _ _ _ _ _ path.2).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- Both actual checked result cells remain live through the complete resident exposure bound. -/
theorem withCheckedExposure_resident_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).Path) :
    (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).peakResidentSpace path ≤
      ((checkedResultShapes width).map SpacePool.ofShape).sum +
        checkedRecoveryActiveSpace model.kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedExposureBody (model := model) spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells)
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction))
    (checkedRecoveryActiveSpace model.kind width)
    (fun cells _ transport _ selected =>
      checkedExposureBody_resident_le _ _ _ _ _ _ _ _ _ selected) path

private theorem checkedExposureBody_auxiliary_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).Path) :
    (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
      inverseSuccess candidate reconstruction).peakAuxiliarySpace path ≤
      checkedRecoveryActiveSpace model.kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (withCheckedInverse_auxiliary_le spec left success inverse path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (withSelectedExposure_auxiliary_le _ _ _ _ _ _ path.2).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- Both actual checked result cells remain live through the complete auxiliary exposure bound. -/
theorem withCheckedExposure_auxiliary_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).Path) :
    (withCheckedExposure (model := model) spec refs inverseSuccess candidate
      reconstruction).peakAuxiliarySpace
      path ≤
      ((checkedResultShapes width).map SpacePool.ofShape).sum +
        checkedRecoveryActiveSpace model.kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedExposureBody (model := model) spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells)
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction))
    (checkedRecoveryActiveSpace model.kind width)
    (fun cells _ transport _ selected =>
      checkedExposureBody_auxiliary_le _ _ _ _ _ _ _ _ _ selected) path

/-- Independent original preparation, checked inversion and three-cell exposure allowance. -/
@[expose] public def singleExposureEnvelope (model : ExecutionModel)
    [BitWord.Selected model] (spec : ModulusSpec
  width) : ResourcePool model :=
  preparationEnvelope model spec + checkedExposureEnvelope model spec

/-- Actual preparation and checked exposure have the original serial dependencies. -/
@[expose] public def singleExposureDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event model → Nat) : Nat :=
  preparationDepthLimit spec duration + checkedExposureDepthLimit spec duration

/- The imported checked-recovery internals stay behind this module's public
space contract. -/
def checkedExposurePersistentSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((checkedResultShapes width).map SpacePool.ofShape).sum +
    checkedRecoveryActiveSpace kind width

/-- Decoder bits end before checked outputs and the selected payload become live. -/
public def singleExposureActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (.bits (width + width)))
    (checkedExposurePersistentSpace kind width)

/-- The complete actual raw exposure retains every stage and scope in its pool bound. -/
theorem singleIntoCells_pool_le (spec : ModulusSpec width)
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
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedExposure (model := model) spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (singleExposureEnvelope model spec) (by
      intro inner cells distinct transport separated selected
      change ResourcePool.ofList
        ((preparationBody (model := model) spec (transport.liftInput input) (preparationRefs
          cells)).eventTrace
          selected.1 ++
          (withCheckedExposure (model := model) spec (preparationRefs cells)
            (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
            (transport.liftWrite reconstruction)).eventTrace selected.2) ≤ _
      rw [ResourcePool.ofList_append]
      exact add_le_add (preparationBody_pool_le _ _ _ selected.1)
        (withCheckedExposure_pool_le _ _ _ _ _ selected.2)) path

/-- The complete actual raw exposure retains every stage and scope in its depth bound. -/
theorem singleIntoCells_depth_le (spec : ModulusSpec width)
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
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedExposure (model := model) spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    duration (singleExposureDepthLimit spec duration) (by
      intro inner cells distinct transport separated selected
      exact Nat.add_le_add (preparationBody_depth_le _ _ _ duration selected.1)
        (withCheckedExposure_depth_le _ _ _ _ _ duration selected.2)) path

set_option maxHeartbeats 400000 in
-- Nested lexical-space maxima require normalization through both allocation scopes.
/-- The complete actual raw exposure retains every stage and scope in its resident bound. -/
theorem singleIntoCells_resident_le (spec : ModulusSpec width)
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
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedExposure (model := model) spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (singleExposureActiveSpace model.kind width) (by
      intro inner cells distinct transport separated selected
      refine (Circuit.peakResidentSpace_seq _ _ selected).le.trans (SpacePool.max_le ?_ ?_)
      · exact (preparationBody_resident_le _ _ _ selected.1).trans
          (add_le_add (SpacePool.le_max_left _ _) le_rfl)
      · exact (withCheckedExposure_resident_le _ _ _ _ _ selected.2).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)) path

set_option maxHeartbeats 400000 in
-- The auxiliary proof follows the same nested allocation expression as the resident bound.
/-- The complete actual raw exposure retains every stage and scope in its auxiliary bound. -/
theorem singleIntoCells_auxiliary_le (spec : ModulusSpec width)
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
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedExposure (model := model) spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (singleExposureActiveSpace model.kind width) (by
      intro inner cells distinct transport separated selected
      refine (Circuit.peakAuxiliarySpace_seq _ _ selected).le.trans (SpacePool.max_le ?_ ?_)
      · exact (preparationBody_auxiliary_le _ _ _ selected.1).trans
          (add_le_add (SpacePool.le_max_left _ _) le_rfl)
      · exact (withCheckedExposure_auxiliary_le _ _ _ _ _ selected.2).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)) path

/-- Unit durations charge preparation and eleven possible recovery and copy instructions. -/
theorem singleIntoCells_unitDepth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (singleIntoCells (model := model) spec input inverseSuccess candidate
      reconstruction).Path) :
    (singleIntoCells (model := model) spec input inverseSuccess candidate reconstruction).depth
      (fun _ => 1) path ≤
      8 * width + 26 + checkedInverseDepthLimit (model := model) spec (fun _ => 1) := by
  exact withCellsFrom_depth_le (Transport.id ctx) (preparationShapes width)
    (fun cells _ transport _ => .seq
      (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs cells))
      (withCheckedExposure (model := model) spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)))
    (fun _ => 1) (8 * width + 26 + checkedInverseDepthLimit (model := model) spec (fun _ => 1)) (by
      intro inner cells distinct transport separated selected
      have prepared := preparationBody_unitDepth_le spec
        (transport.liftInput input) (preparationRefs cells) selected.1
      have later := withCheckedExposure_depth_le spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction) (fun _ => 1) selected.2
      change (withCheckedExposure (model := model) spec (preparationRefs cells)
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction)).depth (fun _ => 1) selected.2 ≤
          checkedInverseDepthLimit (model := model) spec (fun _ => 1) + 11 at later
      change (preparationBody (model := model) spec (transport.liftInput input) (preparationRefs
        cells)).depth
        (fun _ => 1) selected.1 +
        (withCheckedExposure (model := model) spec (preparationRefs cells)
          (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
          (transport.liftWrite reconstruction)).depth (fun _ => 1) selected.2 ≤ _
      omega) path

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
