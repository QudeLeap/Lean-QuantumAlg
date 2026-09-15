/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual resources of the scoped extended-Euclidean active step

The four real scratch cells surround the original fourteen instructions.
Both coefficient updates reuse the same product and subtraction cells, whose
complete widths count in every live-space bound. Lexical allocation adds no
native arithmetic event or serial duration.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual allocation and release retain exactly the original fourteen events. -/
theorem xgcdNativeScopedActive_eventTrace (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive cells zero).Path) :
    (scopedActive cells zero).eventTrace path = activeEvents kind width := by
  exact withCellsFrom_property (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (transportCells transport cells) scratch (transport.liftInput zero))
    (fun _ code => ∀ selected, code.eventTrace selected = activeEvents kind width)
    (fun _ _ _ _ _ available => available)
    (fun scratch _ transport _ selected =>
      xgcdNativeActiveBody_eventTrace _ _ _ selected) path

/-- Native multiplicities belong to this same actual allocated instruction sequence. -/
theorem xgcdNativeScopedActive_resourcePool (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive cells zero).Path) :
    (scopedActive cells zero).resourcePool path =
      ResourcePool.ofList (activeEvents kind width) :=
  congrArg ResourcePool.ofList (xgcdNativeScopedActive_eventTrace cells zero path)

private theorem activeBody_durationDepth (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (activeBody cells scratch zero).Path) :
    (activeBody cells scratch zero).depth duration path =
      ((activeEvents kind width).map duration).sum := by
  simp [activeBody, coefficientUpdateBody, activeEvents, coefficientUpdateEvents,
    Circuit.depth, Circuit.eventDepth, DepthExpr.depthEval, ClassicalOp.event,
    ClassicalOp.label, GCD.divisionOp, activeResizeQuotientOp, coefficientProductOp,
    coefficientSubtractOp, coefficientCopyOp,
    GCD.rotateSecondOp, GCD.takeRemainderOp, GCD.testActiveOp, GCD.negateActiveOp,
    add_assoc]

/-- Arbitrary native durations retain the original complete serial dependency chain. -/
theorem xgcdNativeScopedActive_durationDepth (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (scopedActive cells zero).Path) :
    (scopedActive cells zero).depth duration path =
      ((activeEvents kind width).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (transportCells transport cells) scratch (transport.liftInput zero))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((activeEvents kind width).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun scratch _ transport _ selected => activeBody_durationDepth _ _ _ duration selected) path

/-- The actual four scratch scopes retain the original fourteen unit-duration instructions. -/
theorem xgcdNativeScopedActive_unitDepth (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive cells zero).Path) :
    (scopedActive cells zero).depth (fun _ => 1) path = 14 := by
  rw [xgcdNativeScopedActive_durationDepth]
  rfl

private theorem activeBody_visited (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody cells scratch zero).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (activeBody cells scratch zero).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ ([ctx] ++
    (([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx]))) ++
      (([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx]))) ++
        ([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])))))) at present
  simpa only [List.mem_append, List.mem_singleton, or_self] using present

private theorem activeBody_resident (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody cells scratch zero).Path) :
    (activeBody cells scratch zero).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [activeBody_visited cells scratch zero path visited present]

private theorem activeBody_auxiliary (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody cells scratch zero).Path) :
    (activeBody cells scratch zero).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [activeBody_visited cells scratch zero path visited present]

/-- Every original resident cell and every actual scratch shape is included in the peak. -/
theorem xgcdNativeScopedActive_resident (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive cells zero).Path) :
    (scopedActive cells zero).peakResidentSpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  simpa only [add_zero, scopedActive, withCells] using
    withCellsFrom_resident_le (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (transportCells transport cells) scratch (transport.liftInput zero)) 0
    (by
      intro inner scratch distinct transport separated selected
      simpa only [zero_add] using activeBody_resident
        (transportCells transport cells) scratch (transport.liftInput zero) selected) path

/-- The same four lexical shapes are charged beside all existing auxiliary roles. -/
theorem xgcdNativeScopedActive_auxiliary (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive cells zero).Path) :
    (scopedActive cells zero).peakAuxiliarySpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  simpa only [add_zero, scopedActive, withCells] using
    withCellsFrom_auxiliary_le (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (transportCells transport cells) scratch (transport.liftInput zero)) 0
    (by
      intro inner scratch distinct transport separated selected
      simpa only [zero_add] using activeBody_auxiliary
        (transportCells transport cells) scratch (transport.liftInput zero) selected) path

/-- Reusing the product and updated cells charges three execution-width words only once. -/
theorem xgcdNativeActiveScratch_classicalBits :
    (((activeScratchShapes width).map (SpacePool.ofShape (kind := kind))).sum) .classicalBits =
      2 * width + 3 * PureXGCD.executionCoefficientWidth width := by
  simp [activeScratchShapes, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
