/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual live-space bounds for heterogeneous allocation

Every allocated shape contributes its complete classical encoding while the
body runs. Entry and exit also visit the caller context. The body may allocate
further resources, accounted for by an independent additional space budget.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

private theorem peak_workspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (projection : RuntimeCtx kind → SpacePool kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (code : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (path : (Circuit.workspace ctx key shape fresh code).Path) :
    Circuit.peak projection ((Circuit.workspace ctx key shape fresh code).visitedContexts path) =
      SpacePool.max (projection ctx) (Circuit.peak projection (code.visitedContexts path)) := by
  change SpacePool.max (projection ctx)
    (Circuit.peak projection (code.visitedContexts path ++ [ctx])) = _
  rw [Circuit.peak_append]
  apply SpacePool.ext
  intro axis
  change max (projection ctx axis)
    (max (Circuit.peak projection (code.visitedContexts path) axis)
      (max (projection ctx axis) 0)) = _
  change _ = max (projection ctx axis) (Circuit.peak projection (code.visitedContexts path) axis)
  omega

private theorem withCellsFrom_peak_le {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit inner inner)
    (projection : RuntimeCtx kind → SpacePool kind)
    (workspaceSpace : ∀ (inner : RuntimeCtx kind) (key : StorageKey)
      (shape : CShape) (fresh : key ∉ inner.keys),
      projection (inner.addWorkspace key shape fresh) = SpacePool.ofShape shape + projection inner)
    (additional : SpacePool kind)
    (bodyBound : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (path : (body cells distinct innerTransport separated).Path),
      Circuit.peak projection
        ((body cells distinct innerTransport separated).visitedContexts path) ≤
        additional + projection inner)
    (path : (withCellsFrom transport shapes body).Path) :
    Circuit.peak projection ((withCellsFrom transport shapes body).visitedContexts path) ≤
      (shapes.map SpacePool.ofShape).sum + additional + projection ctx := by
  induction shapes generalizing ctx additional with
  | nil =>
      simpa only [withCellsFrom, List.map_nil, List.sum_nil, zero_add]
        using bodyBound _ _ _ _ path
  | cons shape shapes inductionHypothesis =>
      dsimp only [withCellsFrom] at path ⊢
      refine (inductionHypothesis transport _
        (SpacePool.ofShape shape + additional) ?_ path).trans ?_
      · intro inner cells distinct innerTransport separated selected
        rw [peak_workspace]
        refine SpacePool.max_le (le_add_of_nonneg_left zero_le) ?_
        have inside := bodyBound _ _ _ _ selected
        simpa only [workspaceSpace, add_assoc, add_left_comm, add_comm] using inside
      · exact le_of_eq (by simp only [List.map_cons, List.sum_cons]; ac_rfl)

variable {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit inner inner)
    (additional : SpacePool kind)

/-- Resident peak includes all actual allocated shapes and the body's independent extra budget. -/
theorem withCellsFrom_resident_le
    (bodyBound : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (path : (body cells distinct innerTransport separated).Path),
      (body cells distinct innerTransport separated).peakResidentSpace path ≤
        additional + inner.residentSpace)
    (path : (withCellsFrom transport shapes body).Path) :
    (withCellsFrom transport shapes body).peakResidentSpace path ≤
      (shapes.map SpacePool.ofShape).sum + additional + ctx.residentSpace :=
  withCellsFrom_peak_le transport shapes body RuntimeCtx.residentSpace
    RuntimeCtx.residentSpace_addWorkspace additional bodyBound path

/-- Auxiliary peak charges each live workspace cell together with the body's extra allocation. -/
theorem withCellsFrom_auxiliary_le
    (bodyBound : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (path : (body cells distinct innerTransport separated).Path),
      (body cells distinct innerTransport separated).peakAuxiliarySpace path ≤
        additional + inner.auxiliarySpace)
    (path : (withCellsFrom transport shapes body).Path) :
    (withCellsFrom transport shapes body).peakAuxiliarySpace path ≤
      (shapes.map SpacePool.ofShape).sum + additional + ctx.auxiliarySpace :=
  withCellsFrom_peak_le transport shapes body RuntimeCtx.auxiliarySpace
    RuntimeCtx.auxiliarySpace_addWorkspace additional bodyBound path

end QuantumAlg.Execution.ClassicalWorkspace
