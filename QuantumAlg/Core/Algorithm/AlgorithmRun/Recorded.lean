/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete caller records with an empty persistent service

The actual run records the entire incoming caller store before executing its
code. With the unique empty service, this is exactly a caller duplication
followed by an empty-service history label. Equality decisions at either
recording boundary do not change the complete classical-quantum state.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

attribute [local irreducible] storeFintype ExecutionState.mapClassical

/-- Actual execution retains the same full caller store with either empty-service encoding. -/
theorem emptyService_recorded_execute {gates : GateModel} {oracles : OracleModel}
    {pre post : RuntimeCtx .quantum} {shape : CShape}
    [inputDecision : DecidableEq (Store pre × Unit)]
    [recordDecision : DecidableEq (Store pre × Store pre)]
    (run : AlgorithmRun (.quantum gates oracles .empty .empty) pre post shape)
    (Reference : Register)
    (original : ExecutionState (Store pre) (Register.prod pre.register Reference)) :
    run.execute Reference (original.mapClassical (fun stored => (stored, ()))) =
      run.code.execute Reference
        (State.mapHistory (ctx := pre)
          (original.mapClassical (fun stored => (stored, stored)))
          (fun history => ((), history))) := by
  unfold AlgorithmRun.execute State.mapHistory
  apply congrArg (fun initial : State pre Reference (Unit × Store pre) =>
    run.code.execute Reference initial)
  simp only [ExecutionState.executionState_mapClassical_comp_instances
    (result := Classical.decEq _), Function.comp_def]

end

end QuantumAlg.AlgorithmRun
