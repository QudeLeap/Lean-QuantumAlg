/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Embedding.Execution
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Actual embedded final states and supported paths

All observations below refer to the unchanged child program on its projected
initial input. The frame is retained in the external quantum reference, and
classical frame labels are summed without conditioning admission.
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

/-- Each path retains its entire quantum block under the physical coordinate change. -/
lemma embed_pathState_framed :
    ((embed (allowAllocation := allowAllocation) placement child).run.pathState
      environment Reference input.state).reindex
        (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference) =
      child.run.pathState environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state :=
  embed_observe_framed placement child (environment := environment) input
    (fun record => record.2.2.2)

/-- The original child and the caller assign exactly the same mass to each actual path. -/
lemma embed_pathMass_framed (path : child.run.code.Path) :
    (embed (allowAllocation := allowAllocation) placement child).run.pathMass
      environment Reference input.state path =
      child.run.pathMass environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state path := by
  unfold AlgorithmRun.pathMass
  rw [← embed_pathState_framed (allowAllocation := allowAllocation) placement child
    (environment := environment) input]
  exact (ExecutionState.reindex_block_mass _ _ path).symm

/-- Positive caller path mass is precisely positive mass in the original framed child run. -/
lemma embed_supports_framed_iff (path : child.run.code.Path) :
    (embed (allowAllocation := allowAllocation) placement child).run.Supports
      environment Reference input.state path ↔
      child.run.Supports environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state path := by
  unfold AlgorithmRun.Supports
  rw [embed_pathMass_framed placement child (environment := environment) input path]

/-- The caller's final local store and complete reference state equal the child result. -/
lemma embed_finalState_framed :
    (((embed (allowAllocation := allowAllocation) placement child).run.finalState
      environment Reference input.state).mapClassical
        (fun store => (placement.store store).1)).reindex
          (S := localCtx.register.prod (placement.frame.register.prod Reference))
          (placement.referenceBasis Reference) =
      child.run.finalState environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state := by
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact embed_observe_framed placement child (environment := environment) input Prod.fst

end

end QuantumAlg.Algorithm
