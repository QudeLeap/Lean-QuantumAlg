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
theorem xgcdNativeScopedActive_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive (model := model) cells zero).Path) :
    (scopedActive (model := model) cells zero).eventTrace path = activeEvents model width := by
  exact withCellsFrom_property (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (model := model) (transportCells transport cells) scratch (transport.liftInput
        zero))
    (fun _ code => ∀ selected, code.eventTrace selected = activeEvents model width)
    (fun _ _ _ _ _ available => available)
    (fun scratch _ transport _ selected =>
      xgcdNativeActiveBody_eventTrace _ _ _ selected) path

/-- Native multiplicities belong to this same actual allocated instruction sequence. -/
theorem xgcdNativeScopedActive_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive (model := model) cells zero).Path) :
    (scopedActive (model := model) cells zero).resourcePool path =
      ResourcePool.ofList (activeEvents model width) :=
  congrArg ResourcePool.ofList (xgcdNativeScopedActive_eventTrace cells zero path)

private theorem activeBody_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (activeBody (model := model) cells scratch zero).Path) :
    (activeBody (model := model) cells scratch zero).depth duration path =
      ((activeEvents model width).map duration).sum := by
  rcases path with ⟨a, b, ⟨c, d, e, f⟩, ⟨g, h, i, j⟩, k, l, m, n⟩
  simp only [activeBody, coefficientUpdateBody, Circuit.depth_seq,
    BitWord.bitWord_instruction_depth]
  simp only [activeEvents, coefficientUpdateEvents, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]
  rfl

/-- Arbitrary native durations retain the original complete serial dependency chain. -/
theorem xgcdNativeScopedActive_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (scopedActive (model := model) cells zero).Path) :
    (scopedActive (model := model) cells zero).depth duration path =
      ((activeEvents model width).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (model := model) (transportCells transport cells) scratch (transport.liftInput
        zero))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((activeEvents model width).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun scratch _ transport _ selected => activeBody_durationDepth _ _ _ duration selected) path

/-- The actual four scratch scopes retain the original fourteen unit-duration instructions. -/
theorem xgcdNativeScopedActive_unitDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive (model := model) cells zero).Path) :
    (scopedActive (model := model) cells zero).depth (fun _ => 1) path = 14 := by
  rw [xgcdNativeScopedActive_durationDepth]
  rfl

private theorem activeBody_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody (model := model) cells scratch zero).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (activeBody (model := model) cells scratch zero).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ ([ctx] ++
    (([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx]))) ++
      (([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx]))) ++
        ([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])))))) at present
  simpa only [List.mem_append, List.mem_singleton, or_self] using present

private theorem activeBody_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody (model := model) cells scratch zero).Path) :
    (activeBody (model := model) cells scratch zero).peakResidentSpace path ≤ ctx.residentSpace
      := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [activeBody_visited cells scratch zero path visited present]

private theorem activeBody_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody (model := model) cells scratch zero).Path) :
    (activeBody (model := model) cells scratch zero).peakAuxiliarySpace path ≤ ctx.auxiliarySpace
      := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [activeBody_visited cells scratch zero path visited present]

/-- Every original resident cell and every actual scratch shape is included in the peak. -/
theorem xgcdNativeScopedActive_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive (model := model) cells zero).Path) :
    (scopedActive (model := model) cells zero).peakResidentSpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  simpa only [add_zero, scopedActive, withCells] using
    withCellsFrom_resident_le (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (model := model) (transportCells transport cells) scratch (transport.liftInput
        zero)) 0
    (by
      intro inner scratch distinct transport separated selected
      simpa only [zero_add] using activeBody_resident
        (transportCells transport cells) scratch (transport.liftInput zero) selected) path

/-- The same four lexical shapes are charged beside all existing auxiliary roles. -/
theorem xgcdNativeScopedActive_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (scopedActive (model := model) cells zero).Path) :
    (scopedActive (model := model) cells zero).peakAuxiliarySpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  simpa only [add_zero, scopedActive, withCells] using
    withCellsFrom_auxiliary_le (Transport.id ctx) (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (model := model) (transportCells transport cells) scratch (transport.liftInput
        zero)) 0
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
