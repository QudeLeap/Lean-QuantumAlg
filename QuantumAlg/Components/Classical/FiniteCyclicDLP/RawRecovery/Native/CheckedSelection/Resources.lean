/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Resources

/-!
# Actual checked and selected raw-recovery resources

The original two checked output cells stay live through actual inversion and
selected normalized recovery. The real successful recovery contributes nine
events, while failure contributes only optional packing. The independent
allowance includes the original checked modulus loader and all live scopes.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open NumberTheory.Checked.Native Modular.NativePower

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original successful recovery duration includes both products, verification and packing. -/
def selectedRecoveryDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  (2 * multiplyDepth width duration +
    duration (.classicalOperation (.wordBinary .equal width)) +
      duration (.classicalOperation (.nominalEncoding (.packProduct width 1)))) +
        duration (.classicalOperation (.nominalEncoding (.packOption (width + 1))))

/-- Original independent checked-inverse allowance and the complete selected recovery capacity. -/
def checkedRecoveryEnvelope (kind : ProblemKind) (spec : ModulusSpec width) : ResourcePool kind :=
  checkedInverseEnvelope kind spec + ResourcePool.ofList (selectedRecoveryEvents kind width true)

/-- The original checked call and selected normalized recovery have serial dependencies. -/
def checkedRecoveryDepthLimit (spec : ModulusSpec width)
    (duration : Resource.Event kind → Nat) : Nat :=
  checkedInverseDepthLimit spec duration + selectedRecoveryDepthLimit width duration

/-- Checked engine scratch is released before selected payload and normalized arithmetic scratch. -/
def checkedRecoveryActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (((checkedInverseShapes width).map SpacePool.ofShape).sum +
    checkedInverseActiveSpace kind width) (selectedRecoveryScratchSpace width true)

private theorem selected_pool_le (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).resourcePool path ≤
      ResourcePool.ofList (selectedRecoveryEvents kind width true) := by
  rw [withSelectedRecovery_resourcePool]
  cases selected : path.1.1.toBool
  · simp only [selectedRecoveryEvents, Bool.false_eq_true, if_false, if_true, List.nil_append]
    rw [ResourcePool.ofList_append]
    exact le_add_self
  · exact le_rfl

private theorem selected_depth_le (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (duration : Resource.Event kind → Nat)
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).depth duration path ≤
      selectedRecoveryDepthLimit width duration := by
  rw [withSelectedRecovery_durationDepth]
  cases selected : path.1.1.toBool
  · simp only [selectedRecoveryDepthLimit, Bool.false_eq_true, if_false, Nat.zero_add]
    omega
  · exact le_rfl

private theorem selected_scratch_le (selected : Bool) :
    (selectedRecoveryScratchSpace width selected : SpacePool kind) ≤
      selectedRecoveryScratchSpace width true := by
  cases selected
  · exact add_le_add zero_le le_rfl
  · exact le_rfl

private theorem checked_recovery_body_pool_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (result : CWriteRef ctx (OutputShape width))
    (path : (checkedSelectionBody spec left negatedRight modulus success inverse result).Path) :
    (checkedSelectionBody spec left negatedRight modulus success inverse result).resourcePool path ≤
      checkedRecoveryEnvelope kind spec := by
  change ResourcePool.ofList ((withCheckedInverse spec left success inverse).eventTrace path.1 ++
    (withSelectedRecovery (.product left (.product negatedRight (scaleRead inverse))) modulus
      (scaleRead success) result).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (withCheckedInverse_pool_le spec left success inverse path.1)
    (selected_pool_le _ _ _ _ path.2)

/-- Real allocation of both checked result cells adds no fictitious native operations. -/
theorem withCheckedSelection_pool_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (result : CWriteRef ctx (OutputShape width))
    (path : (withCheckedSelection spec refs result).Path) :
    (withCheckedSelection spec refs result).resourcePool path ≤
      checkedRecoveryEnvelope kind spec := by
  exact withCellsFrom_pool_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedSelectionBody spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells) (transport.liftWrite result))
    (checkedRecoveryEnvelope kind spec)
    (fun cells _ transport _ selected => checked_recovery_body_pool_le _ _ _ _ _ _ _ selected) path

private theorem checked_recovery_body_depth_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (result : CWriteRef ctx (OutputShape width)) (duration : Resource.Event kind → Nat)
    (path : (checkedSelectionBody spec left negatedRight modulus success inverse result).Path) :
    (checkedSelectionBody spec left negatedRight modulus success inverse result).depth
      duration path ≤ checkedRecoveryDepthLimit spec duration :=
  Nat.add_le_add (withCheckedInverse_depth_le spec left success inverse duration path.1)
    (selected_depth_le _ _ _ _ duration path.2)

/-- Actual stored success selects a serial recovery whose original duration is fully charged. -/
theorem withCheckedSelection_depth_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (result : CWriteRef ctx (OutputShape width))
    (duration : Resource.Event kind → Nat) (path : (withCheckedSelection spec refs result).Path) :
    (withCheckedSelection spec refs result).depth duration path ≤
      checkedRecoveryDepthLimit spec duration := by
  exact withCellsFrom_depth_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedSelectionBody spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells) (transport.liftWrite result))
    duration (checkedRecoveryDepthLimit spec duration)
    (fun cells _ transport _ selected =>
      checked_recovery_body_depth_le _ _ _ _ _ _ _ duration selected) path

private theorem checked_recovery_body_resident_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (result : CWriteRef ctx (OutputShape width))
    (path : (checkedSelectionBody spec left negatedRight modulus success inverse result).Path) :
    (checkedSelectionBody spec left negatedRight modulus success inverse result).peakResidentSpace
      path ≤ checkedRecoveryActiveSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (withCheckedInverse_resident_le spec left success inverse path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (withSelectedRecovery_resident _ _ _ _ path.2).le.trans
      (add_le_add ((selected_scratch_le _).trans (SpacePool.le_max_right _ _)) le_rfl)

private theorem checked_recovery_body_auxiliary_le (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (result : CWriteRef ctx (OutputShape width))
    (path : (checkedSelectionBody spec left negatedRight modulus success inverse result).Path) :
    (checkedSelectionBody spec left negatedRight modulus success inverse result).peakAuxiliarySpace
      path ≤ checkedRecoveryActiveSpace kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (withCheckedInverse_auxiliary_le spec left success inverse path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (withSelectedRecovery_auxiliary _ _ _ _ path.2).le.trans
      (add_le_add ((selected_scratch_le _).trans (SpacePool.le_max_right _ _)) le_rfl)

/-- Both original checked result cells coexist with the larger actual checked or recovery scope. -/
theorem withCheckedSelection_resident_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (result : CWriteRef ctx (OutputShape width))
    (path : (withCheckedSelection spec refs result).Path) :
    (withCheckedSelection spec refs result).peakResidentSpace path ≤
      ((checkedResultShapes width).map SpacePool.ofShape).sum +
        checkedRecoveryActiveSpace kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedSelectionBody spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells) (transport.liftWrite result))
    (checkedRecoveryActiveSpace kind width)
    (fun cells _ transport _ selected => checked_recovery_body_resident_le _ _ _ _ _ _ _ selected)
    path

/-- Real auxiliary ownership includes both checked result cells and the complete caller context. -/
theorem withCheckedSelection_auxiliary_le (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (result : CWriteRef ctx (OutputShape width))
    (path : (withCheckedSelection spec refs result).Path) :
    (withCheckedSelection spec refs result).peakAuxiliarySpace path ≤
      ((checkedResultShapes width).map SpacePool.ofShape).sum +
        checkedRecoveryActiveSpace kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (checkedResultShapes width)
    (fun cells _ transport _ => checkedSelectionBody spec
      (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells) (transport.liftWrite result))
    (checkedRecoveryActiveSpace kind width)
    (fun cells _ transport _ selected => checked_recovery_body_auxiliary_le _ _ _ _ _ _ _ selected)
    path

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
