/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem.Embedding
import all QuantumAlg.Core.Algorithm.Problem.Embedding
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Input.Oracle.Projection

/-!
# Exact admission of an original child at its placement

The independent parent contract admits exactly the child's unconditional
local input. Keeping or forgetting the frame in the external reference does
not alter validity or joint service initialization. Arbitrary predicates need
no closure under conditioning.
-/

namespace QuantumAlg.Problem

noncomputable section

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
  (placement : ContextEmbedding localCtx caller)
  (problem : Problem model localCtx localCtx shape)
  (environment : model.Environment) (witness : problem.Witness) {Reference : Register}
  (input : Execution.OracleInput model.classicalOracles caller Reference)

/-- The child with its full quantum frame is admitted by precisely the placed contract. -/
public lemma problem_embed_admits_framed_iff :
    (problem.embed placement).Admits environment witness input ↔
      problem.Admits environment witness (placement.framedInput input) := by
  unfold Admits embed
  rw [placement.contextEmbedding_framedInput_caller_localState,
    placement.contextEmbedding_framedInput_localState]
  rfl

/-- Retaining only the original external reference gives the identical admission condition. -/
public lemma problem_embed_admits_local_iff :
    (problem.embed placement).Admits environment witness input ↔
      problem.Admits environment witness (placement.localInput input) := by
  rw [problem_embed_admits_framed_iff]
  unfold Admits
  rw [placement.contextEmbedding_localInput_caller_localState,
    placement.contextEmbedding_localInput_localState]

end

end QuantumAlg.Problem
