/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Effect bounds for the actual finite sequence

A proved contraction for every actual body execution composes along the
existing finite circuit sequence. Histories retain all real intermediate
paths, and the observed effect depends on the actual current Store. The
consumer must establish each body's contraction for its physical code;
the result introduces no independent-sample execution model.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}

private theorem storedEffect_history {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K)
    (effects : Store ctx → Effect (Register.prod ctx.register Reference)) :
    (state.mapHistory update).effectWeight (fun record => effects record.1) =
      state.effectWeight (fun record => effects record.1) := by
  unfold State.mapHistory
  exact ExecutionState.effectWeight_mapClassical_decision _ state _ _

/-- Proven per-round effect contraction bounds the same actual finite execution. -/
theorem forRange_effectWeight_le (count : Nat) (body : Fin count → Circuit ctx ctx)
    (effects : Store ctx → Effect (Register.prod ctx.register Reference))
    (ratio : ℝ) (nonnegative : 0 ≤ ratio)
    (step : ∀ index {H : Type} [Fintype H] (state : State ctx Reference H),
      ((body index).execute Reference state).effectWeight (fun record => effects record.1) ≤
        ratio * state.effectWeight (fun record => effects record.1))
    {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((forRange count body).execute Reference state).effectWeight
        (fun record => effects record.1) ≤
      ratio ^ count * state.effectWeight (fun record => effects record.1) := by
  induction count generalizing H with
  | zero =>
      rw [forRange, execute_id_mapClassical,
        ExecutionState.effectWeight_mapClassical_decision, pow_zero, one_mul]
  | succ count ih =>
      rw [forRange, execute_seq]
      erw [storedEffect_history]
      have tail := ih (fun index => body index.succ) (fun index => step index.succ)
        ((body 0).execute Reference state)
      have head := mul_le_mul_of_nonneg_left (step 0 state) (pow_nonneg nonnegative count)
      exact tail.trans (head.trans_eq (by rw [← mul_assoc, ← pow_succ]))

end

end QuantumAlg.Circuit
