/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding
public import QuantumAlg.Core.Execution.Composition.Resources
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Reference.Spectator
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Circuit.Reference.Frame

/-!
# Native child placement beside an existing retained cell

The retained cell is already present in the caller. Its complete value stays
in the embedding's frame while the existing interpreter executes the original
allocation-free child. Placement does not inspect or rebuild the child syntax.
Every stored value, external reference and off-diagonal state block remains
part of the complete state, and the resident cell is charged throughout.
-/

namespace QuantumAlg.ContextEmbedding

/-- The actual resident complement consists of one retained cell of its declared shape. -/
@[expose] public def retainedFrame {kind : ProblemKind} (key : StorageKey) (shape : CShape) :
    RuntimeCtx kind :=
  RuntimeCtx.empty.addRetained key shape (by simp [RuntimeCtx.keys])

private lemma retainedFrame_disjoint {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    RuntimeCtx.StorageDisjoint ctx (retainedFrame key shape) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.keys [key]
    exact List.disjoint_singleton.mpr fresh
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.physicalIdx []
    exact List.disjoint_nil_right _

/-- Identity storage and wire placement accounts for the existing retained head cell. -/
@[expose] public def retainedCell {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    ContextEmbedding ctx (ctx.addRetained key shape fresh) where
  keys := Function.Embedding.refl _
  physical := Function.Embedding.refl _
  frame := retainedFrame key shape
  separate := by
    rw [runtimeCtx_relabel_refl]
    exact retainedFrame_disjoint ctx key shape fresh
  covers := by
    change ((ctx.relabel _ _).entries ++ (retainedFrame key shape).entries).Perm
      (ctx.addRetained key shape fresh).entries
    rw [runtimeCtx_relabel_refl]
    exact List.perm_append_comm

end QuantumAlg.ContextEmbedding

namespace QuantumAlg.Circuit

noncomputable section

open Execution

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
  (body : Circuit model ctx ctx false)
  (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)

/-- Placement adds no measurement outcome or branch label to the original child's path. -/
public lemma retainedCell_path :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).Path = body.Path := rfl

/-- Every native operation appears in its original chronological order. -/
public lemma retainedCell_eventTrace (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).eventTrace path =
        body.eventTrace path := rfl

/-- Native event multiplicities belong to the same original child and path. -/
public lemma retainedCell_resourcePool (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).resourcePool path =
        body.resourcePool path :=
  resourcePool_embed (ContextEmbedding.retainedCell ctx key shape fresh) body path

private lemma retainedCell_eventDepth_proof (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).eventDepth path =
        body.eventDepth path := rfl

/-- The complete dependency expression is preserved, before choosing event durations. -/
public lemma retainedCell_eventDepth (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).eventDepth path =
        body.eventDepth path :=
  retainedCell_eventDepth_proof body key shape fresh path

private lemma retainedCell_depth_proof
    (duration : Resource.Event model → Nat) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).depth duration path =
        body.depth duration path := rfl

/-- Exact depth is preserved for every assignment of actual event durations. -/
public lemma retainedCell_depth (duration : Resource.Event model → Nat) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).depth duration path =
        body.depth duration path :=
  retainedCell_depth_proof body key shape fresh duration path

/-- The canonical quantum time uses the original child's full dependency expression. -/
public lemma retainedCell_quantumTime (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).quantumTime path =
        body.quantumTime path :=
  quantumTime_embed (ContextEmbedding.retainedCell ctx key shape fresh) body path

private lemma retainedCell_visitedContexts_proof (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).visitedContexts path =
        [ctx.addRetained key shape fresh] := rfl

/-- The entire caller context, including the retained cell, is live throughout the call. -/
public lemma retainedCell_visitedContexts (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).visitedContexts path =
        [ctx.addRetained key shape fresh] :=
  retainedCell_visitedContexts_proof body key shape fresh path

/-- Resident space includes the cell's full shape and every original context entry. -/
public lemma retainedCell_peakResidentSpace (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).peakResidentSpace path =
        SpacePool.ofShape shape + ctx.residentSpace :=
  (peakResidentSpace_embed (ContextEmbedding.retainedCell ctx key shape fresh) body path).trans
    (RuntimeCtx.residentSpace_addRetained ctx key shape fresh)

/-- The retained storage role contributes its complete auxiliary encoding capacity. -/
public lemma retainedCell_peakAuxiliarySpace (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.retainedCell ctx key shape fresh) body).peakAuxiliarySpace path =
        SpacePool.ofShape shape + ctx.auxiliarySpace :=
  (peakAuxiliarySpace_embed (ContextEmbedding.retainedCell ctx key shape fresh) body path).trans
    (RuntimeCtx.auxiliarySpace_addRetained ctx key shape fresh)

open scoped Classical in
/-- Exact full-state execution keeps arbitrary cell values and every external correlation. -/
public lemma retainedCell_execute (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × History)) :
    let placement := ContextEmbedding.retainedCell ctx key shape fresh
    (Circuit.embed (allowAllocation := allowAllocation) placement body).execute environment
      Reference state =
      placement.join
        ((body.execute environment (Register.prod placement.frame.register Reference)
          ((placement.split state).mapClassical (fun record =>
            (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))).mapClassical
          (fun record =>
            (record.1, (record.2.2.1.1,
              (record.2.1, (record.2.2.1.2, record.2.2.2)))))) :=
  circuit_execute_embed (ContextEmbedding.retainedCell ctx key shape fresh)
    body (environment := environment) Reference state

open scoped Classical in
/-- The complete retained-cell and external-reference observation remains unchanged. -/
lemma retainedCell_frameObservation (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × History)) :
    let placement := ContextEmbedding.retainedCell ctx key shape fresh
    ExecutionState.referenceObservation
      (placement.split
        ((Circuit.embed (allowAllocation := allowAllocation) placement body).execute
          environment Reference state))
      (fun record => (record.2.1, record.2.2.2.1)) =
      (placement.split state).referenceObservation
        (fun record => (record.2.1, record.2.2.2)) :=
  execute_embed_frameObservation
    (ContextEmbedding.retainedCell ctx key shape fresh) body environment Reference state

end

end QuantumAlg.Circuit
