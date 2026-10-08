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

variable {kind : ProblemKind}

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

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Identity visits exactly its unchanged caller context. -/
theorem peakResidentSpace_id
    (path : (Circuit.id (model := model) ctx).Path) :
    (Circuit.id (model := model) ctx).peakResidentSpace path = ctx.residentSpace :=
  SpacePool.max_zero _

/-- Identity preserves exactly the caller's existing auxiliary roles. -/
theorem peakAuxiliarySpace_id
    (path : (Circuit.id (model := model) ctx).Path) :
    (Circuit.id (model := model) ctx).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  SpacePool.max_zero _

/-- A unitary word keeps the complete caller-visible resident context live. -/
theorem peakResidentSpace_unitary
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {quantumCtx : RuntimeCtx .quantum}
    (program : UnitaryCircuit gates oracles quantumCtx.quantumLayout)
    (path : (Circuit.unitary (operations := operations)
      (classicalOracles := classicalOracles) program).Path) :
    (Circuit.unitary (operations := operations)
      (classicalOracles := classicalOracles) program).peakResidentSpace path =
      quantumCtx.residentSpace :=
  SpacePool.max_zero _

/-- A unitary word introduces no caller-visible auxiliary storage. -/
theorem peakAuxiliarySpace_unitary
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {quantumCtx : RuntimeCtx .quantum}
    (program : UnitaryCircuit gates oracles quantumCtx.quantumLayout)
    (path : (Circuit.unitary (operations := operations)
      (classicalOracles := classicalOracles) program).Path) :
    (Circuit.unitary (operations := operations)
      (classicalOracles := classicalOracles) program).peakAuxiliarySpace path =
      quantumCtx.auxiliarySpace :=
  SpacePool.max_zero _

/-- One Z measurement writes an existing cell without changing resident space. -/
theorem peakResidentSpace_measureZ
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {quantumCtx : RuntimeCtx .quantum} (wire : Fin quantumCtx.systemCount)
    (output : CWriteRef quantumCtx
      (.finite (quantumCtx.quantumLayout.wire wire).dimension))
    (path : (Circuit.measureZ (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) wire output).Path) :
    (Circuit.measureZ (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      wire output).peakResidentSpace path = quantumCtx.residentSpace :=
  SpacePool.max_zero _

/-- One Z measurement writes an existing cell without changing auxiliary space. -/
theorem peakAuxiliarySpace_measureZ
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {quantumCtx : RuntimeCtx .quantum} (wire : Fin quantumCtx.systemCount)
    (output : CWriteRef quantumCtx
      (.finite (quantumCtx.quantumLayout.wire wire).dimension))
    (path : (Circuit.measureZ (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) wire output).Path) :
    (Circuit.measureZ (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      wire output).peakAuxiliarySpace path = quantumCtx.auxiliarySpace :=
  SpacePool.max_zero _

/-- Retaining a cell peaks at the complete retained resident context. -/
theorem peakResidentSpace_retain (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (path : (Circuit.retain (model := model) ctx key shape fresh).Path) :
    (Circuit.retain (model := model) ctx key shape fresh).peakResidentSpace path =
      (ctx.addRetained key shape fresh).residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max (ctx.addRetained key shape fresh).residentSpace 0) = _
  rw [SpacePool.max_zero]
  apply SpacePool.max_eq_right
  rw [RuntimeCtx.residentSpace_addRetained]
  exact le_add_of_nonneg_left zero_le

/-- Retaining a cell peaks at the complete retained auxiliary context. -/
theorem peakAuxiliarySpace_retain (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (path : (Circuit.retain (model := model) ctx key shape fresh).Path) :
    (Circuit.retain (model := model) ctx key shape fresh).peakAuxiliarySpace path =
      (ctx.addRetained key shape fresh).auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max (ctx.addRetained key shape fresh).auxiliarySpace 0) = _
  rw [SpacePool.max_zero]
  apply SpacePool.max_eq_right
  rw [RuntimeCtx.auxiliarySpace_addRetained]
  exact le_add_of_nonneg_left zero_le

/-- Every actually visited live context is bounded by that path's resident peak. -/
theorem residentSpace_le_peak_of_visited {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (path : code.Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ code.visitedContexts path) :
    visited.residentSpace ≤ code.peakResidentSpace path :=
  member_le_peak RuntimeCtx.residentSpace _ visited present

/-- Every actually visited context's auxiliary roles contribute to the same path's peak. -/
theorem auxiliarySpace_le_peak_of_visited {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (path : code.Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ code.visitedContexts path) :
    visited.auxiliarySpace ≤ code.peakAuxiliarySpace path :=
  member_le_peak RuntimeCtx.auxiliarySpace _ visited present

/-- A closed classical instruction keeps exactly its existing resident context. -/
theorem peakResidentSpace_classical
    (op : model.classicalOperations.Application ctx)
    (path : (Circuit.classical (model := model) op).Path) :
    (Circuit.classical (model := model) op).peakResidentSpace path = ctx.residentSpace :=
  SpacePool.max_zero _

/-- A closed classical instruction keeps precisely the auxiliary roles of its existing cells. -/
theorem peakAuxiliarySpace_classical
    (op : model.classicalOperations.Application ctx)
    (path : (Circuit.classical (model := model) op).Path) :
    (Circuit.classical (model := model) op).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  SpacePool.max_zero _

/-- A classical-oracle query keeps its hidden state outside caller-addressable storage. -/
theorem peakResidentSpace_classicalQuery
    (application : model.classicalOracles.Application ctx)
    (path : (Circuit.classicalQuery (model := model) application).Path) :
    (Circuit.classicalQuery (model := model) application).peakResidentSpace path =
      ctx.residentSpace :=
  SpacePool.max_zero _

/-- A classical-oracle query adds no caller-visible auxiliary cell. -/
theorem peakAuxiliarySpace_classicalQuery
    (application : model.classicalOracles.Application ctx)
    (path : (Circuit.classicalQuery (model := model) application).Path) :
    (Circuit.classicalQuery (model := model) application).peakAuxiliarySpace path =
      ctx.auxiliarySpace :=
  SpacePool.max_zero _

/-- A branch visits exactly the contexts of the body selected by its stored value. -/
theorem peakResidentSpace_branch {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit model ctx ctx)
    (path : (Circuit.branch input body).Path) :
    (Circuit.branch input body).peakResidentSpace path =
      (body path.1).peakResidentSpace path.2 := rfl

/-- Auxiliary space follows the same selected branch body. -/
theorem peakAuxiliarySpace_branch {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit model ctx ctx)
    (path : (Circuit.branch input body).Path) :
    (Circuit.branch input body).peakAuxiliarySpace path =
      (body path.1).peakAuxiliarySpace path.2 := rfl

/-- Actual lexical entry and exit add the parent context to the body's complete resident peak. -/
theorem peakResidentSpace_workspace (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
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
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
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
