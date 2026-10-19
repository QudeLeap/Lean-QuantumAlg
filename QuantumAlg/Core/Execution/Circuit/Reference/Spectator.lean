/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Spectator
import all QuantumAlg.Core.Execution.Circuit.Reference.Preservation
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# No signalling to a joint classical spectator and quantum reference

A fixed-context child cannot change its inaccessible classical history jointly
with the complete external quantum reference. Both can be arbitrarily
correlated with its live storage and persistent active service. All actual
execution paths are summed within each preserved spectator value, without
postselection or conditional admission [dW19, qcnotes.tex:5381,5394,6827].
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

attribute [local instance] Classical.decEq

/-- An arbitrary finite tag and the old reference are preserved as one joint CQ observation. -/
lemma execute_referenceObservation_tag {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post false)
    (environment : model.Environment)
    {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × (H × Tag.Index))) :
    (code.execute environment Reference state).referenceObservation (fun record => record.2.2.1.2) =
      state.referenceObservation (fun record => record.2.2.2) := by
  apply ExecutionState.ext
  intro tag
  apply DensityOperator.ext
  ext row column
  rw [code.execute_encodedClassicalTag environment state,
    State.referenceObservation_decodeExecutionTag_entry,
    code.execute_referenceMarginal environment,
    ← State.referenceObservation_encodeOracleTag_entry]

/-- Every original history value retains its complete reference matrix after actual execution. -/
lemma execute_referenceObservation_history {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post false)
    (environment : model.Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × H)) :
    (code.execute environment Reference state).referenceObservation (fun record => record.2.2.1) =
      state.referenceObservation (fun record => record.2.2) := by
  let Tag : Register := ⟨H, inferInstance, inferInstance⟩
  have retained := code.execute_referenceObservation_tag environment (Tag := Tag)
    (state.mapHistory (fun record => (record.1, ((), record.2))))
  rw [code.execute_mapHistory environment Reference state
    (fun history => ((), history))] at retained
  simpa only [State.mapHistory, ExecutionState.referenceObservation_mapClassical,
    Function.comp_def] using retained

end

end QuantumAlg.Circuit
