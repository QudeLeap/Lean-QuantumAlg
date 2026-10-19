/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Embedding.Observation
import all QuantumAlg.Core.Algorithm.Composition.Embedding.Distribution
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Marginal
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.State.Marginal.Reference

/-!
# Embedded child observations with the original external reference

Tracing only the complement's quantum register from the exact framed result
gives execution of the original child on the actual localInput. Arbitrary
initial correlations and every original-reference coherence are retained.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
  {shape : CShape} {allowAllocation : Bool}
  (placement : ContextEmbedding localCtx caller)
  (child : Algorithm model localCtx localCtx shape false)
  {environment : model.Environment}
  {Reference : Register} (input : OracleInput model.classicalOracles caller Reference)

/-- The full projected execution is the original child run on its actual local input. -/
lemma embed_execute_local :
    ((placement.split
      ((embed (allowAllocation := allowAllocation) placement child).run.execute
        environment Reference input.state)).mapClassical
          (fun record => (record.1, (record.2.2.1,
            ((placement.store record.2.2.2.1).1, record.2.2.2.2))))).forgetReferenceFrame =
      child.run.execute environment Reference (placement.localInput input).state := by
  calc
    _ = (child.run.execute environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state).forgetReferenceFrame :=
      congrArg (fun current : ExecutionState child.run.Record
          (localCtx.register.prod (placement.frame.register.prod Reference)) =>
        current.forgetReferenceFrame)
        (embed_execute_framed (allowAllocation := allowAllocation) placement child
          (environment := environment) input)
    _ = _ := (child.run.execute_forgetReferenceFrame environment
      (placement.framedInput input).state).symm

/-- Any local classical observation retains the caller's original external reference. -/
lemma embed_observe_local {Result : Type} [Fintype Result] [DecidableEq Result]
    (read : child.run.Record → Result) :
    ((((embed (allowAllocation := allowAllocation) placement child).run.execute
      environment Reference input.state).mapClassical (fun record =>
        read ((placement.store record.1).1,
          (record.2.1, ((placement.store record.2.2.1).1, record.2.2.2))))).reindex
        (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference)).forgetReferenceFrame =
      (child.run.execute environment Reference
        (placement.localInput input).state).mapClassical read := by
  calc
    _ = ((child.run.execute environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state).mapClassical read).forgetReferenceFrame :=
      congrArg (fun current : ExecutionState Result
          (localCtx.register.prod (placement.frame.register.prod Reference)) =>
        current.forgetReferenceFrame)
        (embed_observe_framed (allowAllocation := allowAllocation) placement child
          (environment := environment) input read)
    _ = _ := by
      rw [ExecutionState.forgetReferenceFrame_mapClassical,
        ← child.run.execute_forgetReferenceFrame]
      rfl

/-- Every real path retains exactly its original-reference quantum state. -/
lemma embed_pathState_local :
    (((embed (allowAllocation := allowAllocation) placement child).run.pathState
      environment Reference input.state).reindex
        (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference)).forgetReferenceFrame =
      child.run.pathState environment Reference (placement.localInput input).state :=
  embed_observe_local placement child (environment := environment) input
    (fun record => record.2.2.2)

/-- Caller path mass equals the original child's mass on its unconditioned local input. -/
lemma embed_pathMass_local (path : child.run.code.Path) :
    (embed (allowAllocation := allowAllocation) placement child).run.pathMass
      environment Reference input.state path =
      child.run.pathMass environment Reference (placement.localInput input).state path := by
  unfold AlgorithmRun.pathMass
  rw [← embed_pathState_local (allowAllocation := allowAllocation) placement child
    (environment := environment) input]
  exact ((ExecutionState.forgetReferenceFrame_block_mass _ path).trans
    (ExecutionState.reindex_block_mass _ _ path)).symm

/-- A supported caller path is supported by the original child on the same local input. -/
lemma embed_supports_local_iff (path : child.run.code.Path) :
    (embed (allowAllocation := allowAllocation) placement child).run.Supports
      environment Reference input.state path ↔
      child.run.Supports environment Reference (placement.localInput input).state path := by
  unfold AlgorithmRun.Supports
  rw [embed_pathMass_local placement child (environment := environment) input path]

/-- The complete local final state retains every coherence with the original reference. -/
lemma embed_finalState_local :
    ((((embed (allowAllocation := allowAllocation) placement child).run.finalState
      environment Reference input.state).mapClassical
        (fun store => (placement.store store).1)).reindex
          (S := localCtx.register.prod (placement.frame.register.prod Reference))
          (placement.referenceBasis Reference)).forgetReferenceFrame =
      child.run.finalState environment Reference (placement.localInput input).state := by
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact embed_observe_local placement child (environment := environment) input Prod.fst

/-- Relational success uses the original child run and its actual projected initial store. -/
lemma embed_relationalDistribution_local :
    ((embed (allowAllocation := allowAllocation) placement child).run.relationalDistribution
      environment input).map (fun outcome => ((placement.store outcome.1).1, outcome.2)) =
      child.run.relationalDistribution environment (placement.localInput input) :=
  (embed_relationalDistribution_framed placement child
          (environment := environment) input).trans
    (child.run.relationalDistribution_forgetReferenceFrame environment
      (placement.framedInput input)).symm

end

end QuantumAlg.Algorithm
