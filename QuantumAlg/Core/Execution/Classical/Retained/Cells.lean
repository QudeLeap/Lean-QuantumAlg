/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Transport
public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Heterogeneous retained classical cells

The context and circuit add one actual retained cell of each requested shape.
The returned references name those cells in shape-list order. Unlike lexical
workspaces, the cells remain live when a later circuit changes context.
-/

namespace QuantumAlg.Execution.RetainedCells

open ClassicalWorkspace

/-- One actual retained cell, including its ownership role. -/
public structure Cell {kind : ProblemKind} (ctx : RuntimeCtx kind) (shape : CShape) where
  /-- Writable reference to the retained storage. -/
  ref : CWriteRef ctx shape
  role : ref.toCStorageRef.role = .retained

/-- Heterogeneous references in the same order as their requested shapes. -/
public inductive Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    List CShape → Type where
  | nil : Cells ctx []
  | cons {shape : CShape} {shapes : List CShape}
      (head : Cell ctx shape) (tail : Cells ctx shapes) :
      Cells ctx (shape :: shapes)

namespace Cells

/-- Actual storage keys of the retained references. -/
public def keys {kind : ProblemKind} {ctx : RuntimeCtx kind} {shapes : List CShape} :
    Cells ctx shapes → List StorageKey
  | .nil => []
  | .cons head tail => head.ref.key :: tail.keys

/-- Lift earlier retained references beneath one more retained allocation. -/
public def underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Cells (ctx.addRetained key shape fresh) shapes :=
  match cells with
  | .nil => .nil
  | .cons head tail =>
      .cons
        { ref := head.ref.underRetained key shape fresh
          role := by
            change head.ref.toCStorageRef.role = .retained
            exact head.role }
        (tail.underRetained key shape fresh)

/-- An added retained cell does not rename earlier retained references. -/
public lemma keys_underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (cells.underRetained key shape fresh).keys = cells.keys := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      change head.ref.key :: (tail.underRetained key shape fresh).keys =
        head.ref.key :: tail.keys
      rw [ih]

end Cells

/-- Extend a context with heterogeneous retained cells; list head is added last. -/
@[implicit_reducible]
public def context {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    List CShape → RuntimeCtx kind
  | [] => ctx
  | shape :: tail =>
      let prior := context ctx tail
      prior.addRetained prior.canonicalFreshKey shape prior.canonicalFreshKey_fresh

/-- The actual retained entries added before all caller entries. -/
public def entryPrefix {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    List CShape → List (RuntimeEntry kind)
  | [] => []
  | shape :: tail =>
      let prior := context ctx tail
      .storage prior.canonicalFreshKey .retained shape :: entryPrefix ctx tail

/-- Retention preserves the caller's entries as one exact suffix. -/
public lemma context_entries {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (context ctx shapes).entries = entryPrefix ctx shapes ++ ctx.entries := by
  induction shapes with
  | nil => rfl
  | cons shape tail ih =>
      change .storage (context ctx tail).canonicalFreshKey .retained shape ::
          (context ctx tail).entries =
        (.storage (context ctx tail).canonicalFreshKey .retained shape ::
          entryPrefix ctx tail) ++ ctx.entries
      rw [List.cons_append, ih]

/-- Every allocation is a real `Circuit.retain` instruction. -/
@[implicit_reducible]
public def allocate {model : ExecutionModel} (ctx : RuntimeCtx model.kind) :
    (shapes : List CShape) → Circuit model ctx (context ctx shapes)
  | [] => .id ctx
  | shape :: tail =>
      let prior := context ctx tail
      .seq (allocate ctx tail)
        (.retain prior prior.canonicalFreshKey shape prior.canonicalFreshKey_fresh)

/-- Canonical initial store of the very same retained allocations. -/
public def pushStore {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    (shapes : List CShape) → Store ctx → Store (context ctx shapes)
  | [], store => store
  | shape :: tail, store =>
      let prior := context ctx tail
      (pushStore ctx tail store).pushRetained prior.canonicalFreshKey shape
        prior.canonicalFreshKey_fresh

/-- Typed references to precisely the cells added by `allocate`. -/
@[implicit_reducible]
public def references {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    (shapes : List CShape) → Cells (context ctx shapes) shapes
  | [] => .nil
  | shape :: tail =>
      let prior := context ctx tail
      let key := prior.canonicalFreshKey
      let fresh := prior.canonicalFreshKey_fresh
      .cons { ref := CWriteRef.retainedHead prior key shape fresh
              role := rfl }
        ((references ctx tail).underRetained key shape fresh)

/-- Lift every caller reference through the same actual retained allocations. -/
public def transport {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    (shapes : List CShape) → Transport ctx (context ctx shapes)
  | [] => Transport.id ctx
  | shape :: tail =>
      let prior := context ctx tail
      let before := transport ctx tail
      { liftStorage := fun ref => (before.liftStorage ref).underRetained
          prior.canonicalFreshKey shape prior.canonicalFreshKey_fresh
        liftStorage_key := fun ref => before.liftStorage_key ref
        liftStorage_role := fun ref => before.liftStorage_role ref }

/-- The new keys form the exact prefix of the final live context. -/
public lemma references_keys_append_base {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (references ctx shapes).keys ++ ctx.keys = (context ctx shapes).keys := by
  induction shapes with
  | nil => rfl
  | cons shape tail ih =>
      change (context ctx tail).canonicalFreshKey ::
          ((references ctx tail).underRetained
            (context ctx tail).canonicalFreshKey shape
            (context ctx tail).canonicalFreshKey_fresh).keys ++ ctx.keys =
        (context ctx tail).canonicalFreshKey :: (context ctx tail).keys
      rw [Cells.keys_underRetained, List.cons_append, ih]

/-- All retained cells have physically distinct keys. -/
public lemma references_keys_nodup {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (references ctx shapes).keys.Nodup := by
  have all : ((references ctx shapes).keys ++ ctx.keys).Nodup := by
    rw [references_keys_append_base]
    exact (context ctx shapes).keysNodup
  exact List.Nodup.of_append_left all

/-- Every new key is distinct from every preexisting caller key. -/
public lemma references_keys_disjoint_base {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    List.Disjoint (references ctx shapes).keys ctx.keys := by
  have all : ((references ctx shapes).keys ++ ctx.keys).Nodup := by
    rw [references_keys_append_base]
    exact (context ctx shapes).keysNodup
  exact List.disjoint_of_nodup_append all

/-- Retained classical cells preserve every original quantum wire. -/
public lemma context_quantumWires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (context ctx shapes).quantumWires = ctx.quantumWires := by
  induction shapes with
  | nil => rfl
  | cons shape tail ih =>
      rw [context, RuntimeCtx.quantumWires_addRetained, ih]

/-- The ordered physical wire layout is unchanged by retained storage. -/
public lemma context_quantumLayout_wires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (context ctx shapes).quantumLayout.wires = ctx.quantumLayout.wires := by
  simpa only [RuntimeCtx.quantumLayout_wires] using context_quantumWires ctx shapes

/-- Allocation emits no native gate or classical instruction events. -/
public lemma allocate_eventTrace {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    (path : (allocate (model := model) ctx shapes).Path) :
    (allocate (model := model) ctx shapes).eventTrace path = [] := by
  induction shapes with
  | nil => rfl
  | cons shape tail ih =>
      change (allocate (model := model) ctx tail).eventTrace path.1 ++ [] = []
      rw [ih, List.append_nil]

/-- Retention has zero event duration while its cells count in live space. -/
public lemma allocate_depth {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    (duration : Resource.Event model → Nat)
    (path : (allocate (model := model) ctx shapes).Path) :
    (allocate (model := model) ctx shapes).depth duration path = 0 := by
  induction shapes with
  | nil => rfl
  | cons shape tail ih =>
      change (allocate (model := model) ctx tail).depth duration path.1 + 0 = 0
      rw [ih, Nat.add_zero]

/-- Resident space includes exactly the encoded size of every retained shape. -/
public lemma context_residentSpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (context ctx shapes).residentSpace =
      (shapes.map (SpacePool.ofShape (kind := kind))).sum + ctx.residentSpace := by
  induction shapes with
  | nil => simp only [context, List.map_nil, List.sum_nil, zero_add]
  | cons shape tail ih =>
      rw [context, RuntimeCtx.residentSpace_addRetained, ih]
      simp only [List.map_cons, List.sum_cons]
      ac_rfl

/-- Auxiliary space also includes every actual retained shape. -/
public lemma context_auxiliarySpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (context ctx shapes).auxiliarySpace =
      (shapes.map (SpacePool.ofShape (kind := kind))).sum + ctx.auxiliarySpace := by
  induction shapes with
  | nil => simp only [context, List.map_nil, List.sum_nil, zero_add]
  | cons shape tail ih =>
      rw [context, RuntimeCtx.auxiliarySpace_addRetained, ih]
      simp only [List.map_cons, List.sum_cons]
      ac_rfl

end QuantumAlg.Execution.RetainedCells
