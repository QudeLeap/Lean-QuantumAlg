/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Reference.Spectator
import all QuantumAlg.Core.Execution.Composition.Laws

/-!
# Complete physical-frame observations after embedded execution

The inaccessible frame consists of its original classical store, every one
of its physical quantum systems, and the external reference. Existing
mathematical history stays jointly present. The actual embedded child leaves
this complete observation unchanged even when it is correlated with the
child's local store, active service, or quantum systems
[dW19, qcnotes.tex:389,5381,6827].
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

attribute [local instance] Classical.decEq

/-- Physical embedding preserves the whole frame and spectator history in one CQ state. -/
lemma execute_embed_frameObservation {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind} {allowAllocation : Bool}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false) (environment : model.Environment)
    (Reference : Register)
    {H : Type} [Fintype H] (state : State caller Reference (model.HiddenState × H)) :
    ExecutionState.referenceObservation
      (placement.split
        ((Circuit.embed (allowAllocation := allowAllocation) placement body).execute
        environment Reference state))
      (fun record => (record.2.1, record.2.2.2.1)) =
      (placement.split state).referenceObservation
        (fun record => (record.2.1, record.2.2.2)) := by
  have retained := body.execute_referenceObservation_history environment
    ((placement.split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))
  rw [circuit_execute_embed, placement.contextEmbedding_split_join,
    ExecutionState.referenceObservation_mapClassical]
  simpa only [ExecutionState.referenceObservation_mapClassical, Function.comp_def] using retained

end

end QuantumAlg.Circuit
