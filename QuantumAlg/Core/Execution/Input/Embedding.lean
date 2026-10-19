/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input
public import QuantumAlg.Core.Execution.Context.Embedding
public import QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Context.Embedding

/-!
# Caller observations at an actual physical placement

The input to a local state promise retains the caller's original external
reference. The physical complement is traced out and its classical cells are
summed, without conditioning or allocating storage [dW19, qcnotes.tex:5381,6827].
This mathematical observation depends only on the placement and original input.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference : Register}

/-- Projecting the actual caller onto its local subsystem preserves normalization. -/
public lemma contextEmbedding_projectInput_normalized (input : Input caller Reference) :
    (((input.state.mapClassical placement.store).reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).forgetReferenceFrame.mapClassical
        Prod.fst).IsNormalized :=
  (ExecutionState.mapClassical_mass _ _).trans
    ((ExecutionState.executionState_forgetReferenceFrame_mass _).trans
      ((ExecutionState.reindex_mass _ _).trans
        ((ExecutionState.mapClassical_mass _ _).trans input.normalized)))

/-- Observe the placed input with exactly the original external reference. -/
@[expose] public def projectInput (input : Input caller Reference) : Input localCtx Reference where
  state := ((input.state.mapClassical placement.store).reindex
    (S := localCtx.register.prod (placement.frame.register.prod Reference))
    (placement.referenceBasis Reference)).forgetReferenceFrame.mapClassical Prod.fst
  normalized := placement.contextEmbedding_projectInput_normalized input

end

end QuantumAlg.ContextEmbedding
