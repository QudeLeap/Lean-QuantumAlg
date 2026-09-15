/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Live-space composition for actual execution traces

Each visited context contributes to the actual peak. A lexical workspace
visits its parent on entry and exit and every context of its actual body in
between. Its peak is therefore the maximum of the parent and body peaks.
These are laws of the existing trace, with all native dimension coordinates.
-/

namespace QuantumAlg.Circuit

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem member_le_peak (projection : RuntimeCtx kind → SpacePool kind)
    (contexts : List (RuntimeCtx kind)) (visited : RuntimeCtx kind)
    (present : visited ∈ contexts) : projection visited ≤ peak projection contexts := by
  induction contexts with
  | nil => exact False.elim (List.not_mem_nil present)
  | cons head tail ih =>
      rcases List.mem_cons.mp present with same | later
      · subst visited
        exact SpacePool.le_max_left _ _
      · exact (ih later).trans (SpacePool.le_max_right _ _)

/-- Every actually visited live context is bounded by that path's resident peak. -/
theorem residentSpace_le_peak_of_visited {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (path : code.Path) (visited : RuntimeCtx kind)
    (present : visited ∈ code.visitedContexts path) :
    visited.residentSpace ≤ code.peakResidentSpace path :=
  member_le_peak RuntimeCtx.residentSpace _ visited present

/-- Every actually visited context's auxiliary roles contribute to the same path's peak. -/
theorem auxiliarySpace_le_peak_of_visited {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (path : code.Path) (visited : RuntimeCtx kind)
    (present : visited ∈ code.visitedContexts path) :
    visited.auxiliarySpace ≤ code.peakAuxiliarySpace path :=
  member_le_peak RuntimeCtx.auxiliarySpace _ visited present

/-- A closed classical instruction keeps exactly its existing resident context. -/
theorem peakResidentSpace_classical {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (path : (Circuit.classical op).Path) :
    (Circuit.classical op).peakResidentSpace path = ctx.residentSpace :=
  SpacePool.max_zero _

/-- A closed classical instruction keeps precisely the auxiliary roles of its existing cells. -/
theorem peakAuxiliarySpace_classical {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (path : (Circuit.classical op).Path) :
    (Circuit.classical op).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  SpacePool.max_zero _

/-- Actual lexical entry and exit add the parent context to the body's complete resident peak. -/
theorem peakResidentSpace_workspace (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (path : (Circuit.workspace ctx key shape fresh body).Path) :
    (Circuit.workspace ctx key shape fresh body).peakResidentSpace path =
      SpacePool.max ctx.residentSpace (body.peakResidentSpace path) := by
  change SpacePool.max ctx.residentSpace
    (peak RuntimeCtx.residentSpace (body.visitedContexts path ++ [ctx])) = _
  rw [peak_append]
  apply SpacePool.ext
  intro axis
  change max (ctx.residentSpace axis)
    (max (body.peakResidentSpace path axis) (max (ctx.residentSpace axis) 0)) = _
  change _ = max (ctx.residentSpace axis) (body.peakResidentSpace path axis)
  omega

/-- The same actual lexical trace includes every auxiliary cell while it is live. -/
theorem peakAuxiliarySpace_workspace (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (path : (Circuit.workspace ctx key shape fresh body).Path) :
    (Circuit.workspace ctx key shape fresh body).peakAuxiliarySpace path =
      SpacePool.max ctx.auxiliarySpace (body.peakAuxiliarySpace path) := by
  change SpacePool.max ctx.auxiliarySpace
    (peak RuntimeCtx.auxiliarySpace (body.visitedContexts path ++ [ctx])) = _
  rw [peak_append]
  apply SpacePool.ext
  intro axis
  change max (ctx.auxiliarySpace axis)
    (max (body.peakAuxiliarySpace path axis) (max (ctx.auxiliarySpace axis) 0)) = _
  change _ = max (ctx.auxiliarySpace axis) (body.peakAuxiliarySpace path axis)
  omega

end QuantumAlg.Circuit
