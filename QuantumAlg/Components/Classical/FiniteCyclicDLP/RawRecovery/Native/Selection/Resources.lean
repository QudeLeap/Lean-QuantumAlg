/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Native.Resources

/-!
# Actual selected-recovery resources

The stored branch path incurs eight recovery instructions only on success.
Both paths pay the final optional-result pack and the actual live payload
cell. The recovery scratch is allocated only by the successful native path.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution Modular.NativePower NormalizedRecovery.Native

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact chronological events selected by the original stored inverse-status bit. -/
def selectedRecoveryEvents (kind : ProblemKind) (width : Nat) (selected : Bool) :
    List (Resource.Event kind) :=
  (if selected then recoveryEvents kind width else []) ++
    [.classicalOperation (.nominalEncoding (.packOption (width + 1)))]

/-- The actual path performs recovery only on success, followed by the common optional pack. -/
theorem withSelectedRecovery_eventTrace
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).eventTrace path =
      selectedRecoveryEvents kind width path.1.1.toBool := by
  rcases path with ⟨⟨value, chosen⟩, packed⟩
  cases value with
  | bit value => cases value <;> rfl

/-- The native resource pool follows that same actual selected event trace. -/
theorem withSelectedRecovery_resourcePool
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).resourcePool path =
      ResourcePool.ofList (selectedRecoveryEvents kind width path.1.1.toBool) := by
  exact congrArg ResourcePool.ofList (withSelectedRecovery_eventTrace input modulus success output
    path)

/-- Exactly nine native events on success and one on failure. -/
theorem withSelectedRecovery_eventCount
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    ((withSelectedRecovery input modulus success output).eventTrace path).length =
      if path.1.1.toBool then 9 else 1 := by
  rcases path with ⟨⟨value, chosen⟩, packed⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Arbitrary durations charge the original selected arithmetic and common final materialization. -/
theorem withSelectedRecovery_durationDepth
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (duration : Resource.Event kind → Nat)
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).depth duration path =
      (if path.1.1.toBool then 2 * multiplyDepth width duration +
        duration (.classicalOperation (.wordBinary .equal width)) +
          duration (.classicalOperation (.nominalEncoding (.packProduct width 1))) else 0) +
            duration (.classicalOperation (.nominalEncoding (.packOption (width + 1)))) := by
  rcases path with ⟨⟨value, chosen⟩, packed⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · change (withRecovery (underSelection input width) (underSelection modulus width)
          (selectionPayloadCell ctx width)).depth duration chosen + _ = _
        exact congrArg
          (fun elapsed => elapsed +
            duration (.classicalOperation (.nominalEncoding (.packOption (width + 1)))))
          (withRecovery_durationDepth (underSelection input width) (underSelection modulus width)
            (selectionPayloadCell ctx width) duration chosen)

/-- Unit-duration dependency depth equals the actual selected event count. -/
theorem withSelectedRecovery_depth (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).depth (fun _ => 1) path =
      if path.1.1.toBool then 9 else 1 := by
  rcases path with ⟨⟨value, chosen⟩, packed⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Real persistent payload space and selected arithmetic scratch. -/
def selectedRecoveryScratchSpace {kind : ProblemKind} (width : Nat) (selected : Bool) :
    SpacePool kind :=
  (if selected then recoveryScratchSpace width else 0) +
    SpacePool.ofShape (FiniteCyclicDLP.OutputShape width)

private theorem selectedRecoveryPlaced_resident
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (selectedRecoveryPlaced input modulus success output).Path) :
    (selectedRecoveryPlaced input modulus success output).peakResidentSpace path =
      (if path.1.1.toBool then recoveryScratchSpace width else 0) +
        (selectionCtx ctx width).residentSpace := by
  rcases path with ⟨⟨value, chosen⟩, packed⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max (selectionCtx ctx width).residentSpace
          (SpacePool.max (selectionCtx ctx width).residentSpace 0) =
            0 + (selectionCtx ctx width).residentSpace
        simp only [SpacePool.max_zero, SpacePool.max_self, zero_add]
      · have combined := Circuit.peakResidentSpace_seq
          (.branch (underSelection success width)
            (selectedRecoveryChoice (underSelection input width) (underSelection modulus width)
              (selectionPayloadCell ctx width)))
          (.classical (selectedRecoveryPackOp (underSelection success width)
            (selectionPayloadCell ctx width) (writeUnderSelection output width)))
          (⟨.bit true, chosen⟩, packed)
        refine combined.trans ?_
        change SpacePool.max
          ((withRecovery (underSelection input width) (underSelection modulus width)
            (selectionPayloadCell ctx width)).peakResidentSpace chosen)
          ((Circuit.classical (selectedRecoveryPackOp (underSelection success width)
            (selectionPayloadCell ctx width) (writeUnderSelection output width))).peakResidentSpace
              packed) = _
        refine (congrArg₂ SpacePool.max
          (withRecovery_resident (underSelection input width) (underSelection modulus width)
            (selectionPayloadCell ctx width) chosen)
          (Circuit.peakResidentSpace_classical
            (selectedRecoveryPackOp (underSelection success width) (selectionPayloadCell ctx width)
              (writeUnderSelection output width)) packed)).trans ?_
        exact SpacePool.max_eq_left le_add_self

/-- Exact resident peak includes original roles, payload and selected recovery scratch. -/
theorem withSelectedRecovery_resident
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).peakResidentSpace path =
      selectedRecoveryScratchSpace width path.1.1.toBool + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh
    (selectedRecoveryPlaced input modulus success output) path).trans
      ((congrArg (SpacePool.max ctx.residentSpace)
        (selectedRecoveryPlaced_resident input modulus success output path)).trans ?_)
  have bounded : ctx.residentSpace ≤
      (if path.1.1.toBool then recoveryScratchSpace width else 0) +
        (selectionCtx ctx width).residentSpace := by
    intro axis
    change ctx.residentSpace axis ≤
      (if path.1.1.toBool then recoveryScratchSpace width else 0) axis +
        (SpacePool.ofShape (FiniteCyclicDLP.OutputShape width) axis + ctx.residentSpace axis)
    omega
  rw [SpacePool.max_eq_right bounded]
  simp only [selectionCtx, RuntimeCtx.residentSpace_addWorkspace,
    selectedRecoveryScratchSpace, add_assoc]

private theorem selectedRecoveryPlaced_auxiliary
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (selectedRecoveryPlaced input modulus success output).Path) :
    (selectedRecoveryPlaced input modulus success output).peakAuxiliarySpace path =
      (if path.1.1.toBool then recoveryScratchSpace width else 0) +
        (selectionCtx ctx width).auxiliarySpace := by
  rcases path with ⟨⟨value, chosen⟩, packed⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max (selectionCtx ctx width).auxiliarySpace
          (SpacePool.max (selectionCtx ctx width).auxiliarySpace 0) =
            0 + (selectionCtx ctx width).auxiliarySpace
        simp only [SpacePool.max_zero, SpacePool.max_self, zero_add]
      · have combined := Circuit.peakAuxiliarySpace_seq
          (.branch (underSelection success width)
            (selectedRecoveryChoice (underSelection input width) (underSelection modulus width)
              (selectionPayloadCell ctx width)))
          (.classical (selectedRecoveryPackOp (underSelection success width)
            (selectionPayloadCell ctx width) (writeUnderSelection output width)))
          (⟨.bit true, chosen⟩, packed)
        refine combined.trans ?_
        change SpacePool.max
          ((withRecovery (underSelection input width) (underSelection modulus width)
            (selectionPayloadCell ctx width)).peakAuxiliarySpace chosen)
          ((Circuit.classical (selectedRecoveryPackOp (underSelection success width)
            (selectionPayloadCell ctx width) (writeUnderSelection output width))).peakAuxiliarySpace
              packed) = _
        refine (congrArg₂ SpacePool.max
          (withRecovery_auxiliary (underSelection input width) (underSelection modulus width)
            (selectionPayloadCell ctx width) chosen)
          (Circuit.peakAuxiliarySpace_classical
            (selectedRecoveryPackOp (underSelection success width) (selectionPayloadCell ctx width)
              (writeUnderSelection output width)) packed)).trans ?_
        exact SpacePool.max_eq_left le_add_self

/-- Exact auxiliary peak includes original roles, payload and selected recovery scratch. -/
theorem withSelectedRecovery_auxiliary
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (withSelectedRecovery input modulus success output).Path) :
    (withSelectedRecovery input modulus success output).peakAuxiliarySpace path =
      selectedRecoveryScratchSpace width path.1.1.toBool + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh
    (selectedRecoveryPlaced input modulus success output) path).trans
      ((congrArg (SpacePool.max ctx.auxiliarySpace)
        (selectedRecoveryPlaced_auxiliary input modulus success output path)).trans ?_)
  have bounded : ctx.auxiliarySpace ≤
      (if path.1.1.toBool then recoveryScratchSpace width else 0) +
        (selectionCtx ctx width).auxiliarySpace := by
    intro axis
    change ctx.auxiliarySpace axis ≤
      (if path.1.1.toBool then recoveryScratchSpace width else 0) axis +
        (SpacePool.ofShape (FiniteCyclicDLP.OutputShape width) axis + ctx.auxiliarySpace axis)
    omega
  rw [SpacePool.max_eq_right bounded]
  simp only [selectionCtx, RuntimeCtx.auxiliarySpace_addWorkspace,
    selectedRecoveryScratchSpace, add_assoc]

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
