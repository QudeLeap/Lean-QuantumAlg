/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range.Effect
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Finite contraction along actual prefixes from the original input

A caller may establish its one-step bound from the actual prescribed input
and borrowed restoration of every real prefix. The finite-loop proof then
uses those same prefixes, without requiring the bound on arbitrary states
whose public classical values need not represent the prescribed problem.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

private theorem storedWeight_seq_assoc {kind : ProblemKind}
    {origin first second final : RuntimeCtx kind}
    (priorCode : Circuit origin first) (middle : Circuit first second)
    (tail : Circuit second final) {Reference : Register} {H : Type} [Fintype H]
    (state : State origin Reference H)
    (effects : Store final → Effect (final.register.prod Reference)) :
    ((priorCode.seq (middle.seq tail)).execute Reference state).effectWeight
        (fun record => effects record.1) =
      (((priorCode.seq middle).seq tail).execute Reference state).effectWeight
        (fun record => effects record.1) := by
  simp only [execute_seq, execute_mapHistory, State.effectWeight_mapHistory]

/-- Uniform bounds on the real prefixes give geometric contraction for that same finite loop. -/
theorem forRange_effectWeight_le_on_actual_prefix {kind : ProblemKind}
    {origin ctx : RuntimeCtx kind} {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference H) (count : Nat) (body : Fin count → Circuit ctx ctx)
    (effects : Store ctx → Effect (ctx.register.prod Reference))
    (ratio : ℝ) (nonnegative : 0 ≤ ratio)
    (step : ∀ (priorCode : Circuit origin ctx) index,
      ((priorCode.seq (body index)).execute Reference initial).effectWeight
          (fun record => effects record.1) ≤
        ratio * (priorCode.execute Reference initial).effectWeight (fun record => effects record.1))
    (priorCode : Circuit origin ctx) :
    ((priorCode.seq (forRange count body)).execute Reference initial).effectWeight
        (fun record => effects record.1) ≤
      ratio ^ count * (priorCode.execute Reference initial).effectWeight
        (fun record => effects record.1) := by
  induction count generalizing priorCode with
  | zero =>
      rw [forRange, execute_seq, pow_zero, one_mul]
      erw [State.effectWeight_mapHistory]
      rw [execute_id_mapClassical, ExecutionState.effectWeight_mapClassical_decision]
  | succ count ih =>
      rw [forRange, storedWeight_seq_assoc]
      have tail := ih (fun index => body index.succ)
        (fun current index => step current index.succ) (priorCode.seq (body 0))
      have head := mul_le_mul_of_nonneg_left (step priorCode 0) (pow_nonneg nonnegative count)
      exact tail.trans (head.trans_eq (by rw [← mul_assoc, ← pow_succ]))

end

end QuantumAlg.Circuit
