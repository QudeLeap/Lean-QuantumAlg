/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Embedding.Execution
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Context.Embedding.References
import all QuantumAlg.Core.Execution.Probability

/-!
# Relational distributions of the original embedded child

Probabilities are obtained from the complete block projection. The original
local input store and actual placed output are retained together, including
arbitrary incoming caller, service and reference correlations.
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

/-- Any observed child distribution is the corresponding marginal of the actual caller run. -/
lemma embed_observationDistribution_framed {Result : Type} [Finite Result]
    (read : child.run.Record → Result) :
    ((embed (allowAllocation := allowAllocation) placement child).run.executionDistribution
      environment input).map (fun record => read ((placement.store record.1).1,
        (record.2.1, ((placement.store record.2.2.1).1, record.2.2.2)))) =
      (child.run.executionDistribution environment (placement.framedInput input)).map read := by
  let : Fintype Result := Fintype.ofFinite Result
  let run := (embed (allowAllocation := allowAllocation) placement child).run
  let readCaller : run.Record → Result := fun record =>
    read ((placement.store record.1).1,
      (record.2.1, ((placement.store record.2.2.1).1, record.2.2.2)))
  apply PMF.ext
  intro result
  have blocks := congrArg (fun current : ExecutionState Result
      (localCtx.register.prod (placement.frame.register.prod Reference)) =>
    (current.block result).mass)
      (embed_observe_framed (allowAllocation := allowAllocation) placement child
        (environment := environment) input read)
  rw [ExecutionState.reindex_block_mass] at blocks
  calc
    _ = ENNReal.ofReal
        (((run.execute environment Reference input.state).mapClassical readCaller).block
          result).mass :=
      (congrArg (fun distribution : PMF Result => distribution result)
        (ExecutionState.toPMF_mapClassical (run.execute environment Reference input.state)
          (run.execute_normalized environment input) readCaller)).symm
    _ = ENNReal.ofReal
        (((child.run.execute environment (placement.frame.register.prod Reference)
          (placement.framedInput input).state).mapClassical read).block result).mass :=
      congrArg ENNReal.ofReal blocks
    _ = _ := congrArg (fun distribution : PMF Result => distribution result)
      (ExecutionState.toPMF_mapClassical
        (child.run.execute environment (placement.frame.register.prod Reference)
          (placement.framedInput input).state)
        (child.run.execute_normalized environment (placement.framedInput input)) read)

/-- The original local input store stays jointly distributed with the actual placed output. -/
lemma embed_relationalDistribution_framed :
    ((embed (allowAllocation := allowAllocation) placement child).run.relationalDistribution
      environment input).map (fun outcome => ((placement.store outcome.1).1, outcome.2)) =
      child.run.relationalDistribution environment (placement.framedInput input) := by
  unfold AlgorithmRun.relationalDistribution
  rw [PMF.map_comp]
  calc
    _ = ((embed (allowAllocation := allowAllocation) placement child).run.executionDistribution
        environment input).map (fun record => ((placement.store record.2.2.1).1,
          child.run.output.eval (placement.store record.1).1)) := by
      apply congrArg (fun read =>
        ((embed (allowAllocation := allowAllocation) placement child).run.executionDistribution
          environment input).map read)
      funext record
      apply congrArg (fun result => ((placement.store record.2.2.1).1, result))
      change (placement.output child.run.output).eval record.1 = _
      simpa only [Prod.eta, Equiv.symm_apply_apply] using
        placement.contextEmbedding_output_eval (placement.store record.1).1
          (placement.store record.1).2 child.run.output
    _ = _ := embed_observationDistribution_framed placement child (environment := environment) input
      (fun record => (record.2.2.1, child.run.result record))

end

end QuantumAlg.Algorithm
