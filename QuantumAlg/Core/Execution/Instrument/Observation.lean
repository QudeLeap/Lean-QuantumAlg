/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Store effects of the same actual circuit execution

An observation changes no instruction or retained record. The effect of a
classical event is the certain or impossible effect on its complete quantum
register, and the execution weight observes the actual returned Store.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- The certain or impossible effect of one original classical event. -/
def recordEventEffect {Record : Type} (R : Register) (event : Record → Bool)
    (record : Record) : Effect R :=
  if event record = true then Effect.one R else Effect.zero R

/-- Observe the Store returned by the actual interpreter, without replacing its channel. -/
def storeEffectWeight {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} {allowAllocation : Bool} {Reference : Register}
    (code : Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (effects : Store ctx → Effect (ctx.register.prod Reference)) : Real :=
  (code.execute environment Reference state).effectWeight (fun record => effects record.1)

end

end QuantumAlg.Execution
