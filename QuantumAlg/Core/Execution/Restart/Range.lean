/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Restart.Deterministic
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Positive actual finite ranges preserve their complete final physical seed
-/

namespace QuantumAlg.Circuit.RestartCleanup

noncomputable section

open Execution

attribute [local instance] Classical.decEq

/-- Every positive finite range ends in the same actual full reset, including its empty tail. -/
lemma constantRange_reinitializedAt {model : ExecutionModel}
    {environment : model.Environment} {ctx : RuntimeCtx model.kind}
    (body : Circuit model ctx ctx) (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : ReinitializedAt body environment seed) (further : Nat) :
    ReinitializedAt (Circuit.forRange (further + 1) (fun _ => body)) environment seed := by
  induction further with
  | zero =>
      exact followedByMapAt (environment := environment) body (Circuit.id ctx) seed fixed
        (fun entry => (entry, ()))
        (by
          intro Reference History _ state
          exact (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans
            (ExecutionState.executionState_mapClassical_congr_decision state _ _
              (by intro entry; rfl) _ _))
  | succ further ih =>
      exact afterAt (environment := environment) body
        (Circuit.forRange (further + 1) (fun _ => body)) seed ih

end

end QuantumAlg.Circuit.RestartCleanup
