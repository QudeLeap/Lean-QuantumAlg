/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.OperationalEquiv
public import QuantumAlg.Core.Execution.Context.Embedding.Retained
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Composition.History
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete sequential execution through the original native placement

One embedded sequence and two successive embedded children have different
circuit trees. Their complete physical execution agrees on the identity path,
including every frame cell, external reference, service state and old history.
No child syntax is recompiled and no cell is allocated by placement.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
  {allowAllocation : Bool}

private lemma execute_embed_history (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false)
    (environment : model.Environment) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State caller Reference (model.HiddenState × H)) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).execute environment
      Reference state =
      placement.join
        ((body.execute environment (Register.prod placement.frame.register Reference)
          ((placement.split state).mapHistory
            (fun record => (record.2.1, (record.1, record.2.2))))).mapHistory
              (fun record =>
                (record.2.1.1, (record.1, (record.2.1.2, record.2.2))))) := by
  rw [circuit_execute_embed]
  apply congrArg placement.join
  dsimp only [State.mapHistory]
  apply pushforward_congr
  apply congrArg (fun input =>
    body.execute environment (Register.prod placement.frame.register Reference) input)
  exact pushforward_congr rfl _

/-- Splitting the first actual call exposes exactly the input history of the next child. -/
private lemma split_execute_embed_history
    (placement : ContextEmbedding localCtx caller)
    (first : Circuit model localCtx localCtx false)
    (environment : model.Environment) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State caller Reference (model.HiddenState × H)) :
    ((placement.split
      ((Circuit.embed (allowAllocation := allowAllocation) placement first).execute
        environment Reference state)).mapHistory
          (fun record => (record.2.1, (record.1, record.2.2)))) =
      (first.execute environment (Register.prod placement.frame.register Reference)
        ((placement.split state).mapHistory
          (fun record => (record.2.1, (record.1, record.2.2))))).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  rw [execute_embed_history, placement.contextEmbedding_split_join]
  simp only [State.mapHistory_comp, Function.comp_def]

/-- Original native children compose as complete physical executions on the same path. -/
public lemma execute_embed_seq (placement : ContextEmbedding localCtx caller)
    (first second : Circuit model localCtx localCtx false)
    (environment : model.Environment) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State caller Reference (model.HiddenState × H)) :
    (Circuit.embed (allowAllocation := allowAllocation) placement
      (first.seq second)).execute environment Reference state =
        ((Circuit.embed (allowAllocation := allowAllocation) placement first).seq
          (Circuit.embed (allowAllocation := allowAllocation) placement second)).execute
            environment Reference state := by
  let localInput := (placement.split state).mapHistory
    (fun record => (record.2.1, (record.1, record.2.2)))
  let localResult := first.execute environment
    (Register.prod placement.frame.register Reference) localInput
  have next := execute_mapHistory second environment
    (Register.prod placement.frame.register Reference) localResult
    (fun history : (Store placement.frame × H) × first.Path =>
      (history.1.1, (history.1.2, history.2)))
  symm
  rw [execute_seq, execute_embed_history, split_execute_embed_history]
  change (placement.join
      ((second.execute environment (Register.prod placement.frame.register Reference)
        (localResult.mapHistory
          (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))))).mapHistory
            (fun record =>
              (record.2.1.1, (record.1, (record.2.1.2, record.2.2)))))).mapHistory
                (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) = _
  rw [next, ← placement.join_mapHistory, execute_embed_history, execute_seq]
  simp only [localInput, localResult, State.mapHistory_comp, Function.comp_def]

/-- Placement preserves an existing complete allocation-free execution certificate. -/
def OperationalEquiv.embed (placement : ContextEmbedding localCtx caller)
    {source target : Circuit model localCtx localCtx false}
    (certificate : OperationalEquiv source target) :
    OperationalEquiv
      (Circuit.embed (allowAllocation := allowAllocation) placement source)
      (Circuit.embed (allowAllocation := allowAllocation) placement target) where
  path := certificate.path
  execute := by
    intro environment Reference H _ state
    rw [execute_embed_history, execute_embed_history,
      certificate.execute, ← placement.join_mapHistory]
    simp only [State.mapHistory_comp, Function.comp_def]
  events := certificate.events
  depth := certificate.depth
  resident := by
    intro path
    rw [peakResidentSpace_embed, peakResidentSpace_embed]
  auxiliary := by
    intro path
    rw [peakAuxiliarySpace_embed, peakAuxiliarySpace_embed]

/-- Sequence placement preserves the entire existing operational-equivalence contract. -/
def embed_seqOperationalEquiv (placement : ContextEmbedding localCtx caller)
    (first second : Circuit model localCtx localCtx false) :
    OperationalEquiv
      (Circuit.embed (allowAllocation := allowAllocation) placement (first.seq second))
      ((Circuit.embed (allowAllocation := allowAllocation) placement first).seq
        (Circuit.embed (allowAllocation := allowAllocation) placement second)) where
  path := Equiv.refl _
  execute := by
    intro environment Reference H _ state
    change _ =
      (((Circuit.embed (allowAllocation := allowAllocation) placement first).seq
        (Circuit.embed (allowAllocation := allowAllocation) placement second)).execute
          environment Reference state).mapHistory _root_.id
    rw [OperationalEquiv.mapHistory_id]
    exact execute_embed_seq placement first second environment Reference state
  events := by intro path; rfl
  depth := by intro duration path; rfl
  resident := by
    intro path
    rw [peakResidentSpace_embed, peakResidentSpace_seq,
      peakResidentSpace_embed, peakResidentSpace_embed, SpacePool.max_self]
  auxiliary := by
    intro path
    rw [peakAuxiliarySpace_embed, peakAuxiliarySpace_seq,
      peakAuxiliarySpace_embed, peakAuxiliarySpace_embed, SpacePool.max_self]

/-- A retained cell uses the same native sequence law without a locality premise. -/
def retainedCell_seqOperationalEquiv
    (first second : Circuit model localCtx localCtx false)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ localCtx.keys) :
    OperationalEquiv
      (Circuit.embed (allowAllocation := allowAllocation)
        (ContextEmbedding.retainedCell localCtx key shape fresh) (first.seq second))
      ((Circuit.embed (allowAllocation := allowAllocation)
        (ContextEmbedding.retainedCell localCtx key shape fresh) first).seq
          (Circuit.embed (allowAllocation := allowAllocation)
            (ContextEmbedding.retainedCell localCtx key shape fresh) second)) :=
  embed_seqOperationalEquiv (ContextEmbedding.retainedCell localCtx key shape fresh) first second

end

end QuantumAlg.Circuit
