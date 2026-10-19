/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.ClassicalTag
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Composition.ClassicalTag.Marginal

/-!
# Actual execution commutes with an external reference partial trace

The theorem follows by decoding each diagonal reference block and summing
its mathematical tag. It imposes no independence, normalization or
admission premise on a conditional slice, and keeps every real record.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

attribute [local instance] Classical.decEq

/-- Tracing an untouched reference factor commutes with the original fixed circuit. -/
lemma execute_forgetReferenceFrame
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) (environment : model.Environment)
    {Reference Frame : Register} {H : Type} [Fintype H]
    (state : State pre (Frame.prod Reference) (model.HiddenState × H)) :
    code.execute environment Reference state.forgetReferenceFrame =
      (code.execute environment (Frame.prod Reference) state).forgetReferenceFrame := by
  calc
    _ = code.execute environment Reference ((State.decodeOracleTag state).mapHistory
        (fun record => (record.1, record.2.1))) :=
      congrArg (code.execute environment Reference)
        (State.decodeOracleTag_forgetReferenceFrame state).symm
    _ = (code.execute environment Reference (State.decodeOracleTag state)).mapHistory
        (fun record => (record.1, (record.2.1.1, record.2.2))) :=
      code.execute_mapHistory environment Reference (State.decodeOracleTag state) Prod.fst
    _ = (State.decodeExecutionTag
        (code.execute environment (Frame.prod Reference) state)).mapHistory
        (fun record => (record.1, (record.2.1.1, record.2.2))) :=
      congrArg (fun current :
          State post Reference (model.HiddenState × ((H × Frame.Index) × code.Path)) =>
        current.mapHistory (fun record => (record.1, (record.2.1.1, record.2.2))))
        (code.execute_decodeReferenceTag environment state)
    _ = _ := State.decodeExecutionTag_forgetReferenceFrame _

end

end QuantumAlg.Circuit
