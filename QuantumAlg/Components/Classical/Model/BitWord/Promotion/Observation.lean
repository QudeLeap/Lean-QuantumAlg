/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Circuit.Effect
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Actual stored observations after a promoted quantum prefix

The selected prefix relabels its finite execution path. A subsequent native
circuit acts on the same complete state and persistent service. Observing
the actual returned store therefore gives the same weighted quantum effect
under every external reference and every previous history.
-/

namespace QuantumAlg.BitWord

noncomputable section

open Execution

/-- A real native suffix observes the same complete quantum blocks after model selection. -/
theorem selectForCircuit_seq_stored_effectWeight {gates : GateModel} {oracles : OracleModel}
    {pre middle post : RuntimeCtx .quantum}
    (first : Circuit (.quantum gates oracles) pre middle)
    (suffix : Circuit (.quantum gates oracles model) middle post)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference
      ((.quantum gates oracles : ExecutionModel).HiddenState × History))
    (effects : Store post → Effect (Register.prod post.register Reference)) :
    (((selectForCircuit first).seq suffix).execute Reference state).effectWeight
        (fun entry => effects entry.1) =
      (suffix.execute Reference (first.execute Reference state)).effectWeight
        (fun entry => effects entry.1) := by
  rw [Circuit.execute_seq, State.effectWeight_mapHistory, selectForCircuit_execute]
  have history := Circuit.execute_mapHistory suffix Reference
    (first.execute Reference state)
    (fun record : History × first.Path =>
      (record.1, selectForCircuitPathEquiv first record.2))
  have observed := congrArg
    (fun output => output.effectWeight (fun entry => effects entry.1)) history
  exact observed.trans (State.effectWeight_mapHistory _ _ _)

end

end QuantumAlg.BitWord
