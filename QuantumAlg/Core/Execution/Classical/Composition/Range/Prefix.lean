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

private lemma storedWeight_seq_assoc {model : ExecutionModel}
    {origin first second final : RuntimeCtx model.kind}
    (priorCode : Circuit model origin first) (middle : Circuit model first second)
    (tail : Circuit model second final) (environment : model.Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State origin Reference (model.HiddenState × H))
    (effects : Store final → Effect (final.register.prod Reference)) :
    ((priorCode.seq (middle.seq tail)).execute environment Reference state).effectWeight
        (fun record => effects record.1) =
      (((priorCode.seq middle).seq tail).execute environment Reference state).effectWeight
        (fun record => effects record.1) := by
  simp only [execute_seq, State.effectWeight_mapHistory]
  rw [execute_mapHistory tail environment Reference
    (middle.execute environment Reference (priorCode.execute environment Reference state))
    (fun history => (history.1.1, (history.1.2, history.2))), State.effectWeight_mapHistory]

private lemma storedWeight_execute_mapHistory {model : ExecutionModel}
    {origin result : RuntimeCtx model.kind}
    (code : Circuit model origin result) (environment : model.Environment)
    {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    (state : State origin Reference (model.HiddenState × H)) (update : H → K)
    (effects : Store result → Effect (result.register.prod Reference)) :
    (code.execute environment Reference
      (state.mapHistory (fun record => (record.1, update record.2)))).effectWeight
        (fun record => effects record.1) =
      (code.execute environment Reference state).effectWeight (fun record => effects record.1) := by
  rw [execute_mapHistory code environment Reference state update, State.effectWeight_mapHistory]

/-- Rebracketing four actual stages leaves every final store observation unchanged. -/
lemma storedWeight_four_stage {model : ExecutionModel}
    {origin first second final result : RuntimeCtx model.kind}
    (setup : Circuit model origin first) (allocation : Circuit model first second)
    (body : Circuit model second final) (packing : Circuit model final result)
    (environment : model.Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference (model.HiddenState × H))
    (effects : Store result → Effect (result.register.prod Reference)) :
    ((setup.seq ((allocation.seq body).seq packing)).execute
      environment Reference initial).effectWeight
        (fun entry => effects entry.1) =
      (packing.execute environment Reference (((setup.seq allocation).seq body).execute
        environment Reference initial)).effectWeight (fun entry => effects entry.1) := by
  simp only [execute_seq, State.effectWeight_mapHistory]
  rw [execute_mapHistory body environment Reference
    (allocation.execute environment Reference (setup.execute environment Reference initial))
    (fun history => (history.1.1, (history.1.2, history.2)))]
  simp only [State.mapHistory_comp, Function.comp_def]
  let state : State final Reference
      (model.HiddenState × (((H × setup.Path) × allocation.Path) × body.Path)) :=
    body.execute environment Reference (allocation.execute environment Reference
      (setup.execute environment Reference initial))
  let leftUpdate : (((H × setup.Path) × allocation.Path) × body.Path) →
      (H × setup.Path) × (allocation.Path × body.Path) :=
    fun history => (history.1.1, (history.1.2, history.2))
  let rightUpdate : (((H × setup.Path) × allocation.Path) × body.Path) →
      H × ((setup.Path × allocation.Path) × body.Path) :=
    fun history => (history.1.1.1, ((history.1.1.2, history.1.2), history.2))
  change (packing.execute environment Reference
      (state.mapHistory (fun record => (record.1, leftUpdate record.2)))).effectWeight
        (fun record => effects record.1) =
    (packing.execute environment Reference
      (state.mapHistory (fun record => (record.1, rightUpdate record.2)))).effectWeight
        (fun record => effects record.1)
  rw [storedWeight_execute_mapHistory packing environment state leftUpdate effects,
    storedWeight_execute_mapHistory packing environment state rightUpdate effects]

/-- Uniform bounds on the real prefixes give geometric contraction for that same finite loop. -/
lemma forRange_effectWeight_le_on_actual_prefix {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind} {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference (model.HiddenState × H))
    (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (environment : model.Environment)
    (effects : Store ctx → Effect (ctx.register.prod Reference))
    (ratio : ℝ) (nonnegative : 0 ≤ ratio)
    (step : ∀ (priorCode : Circuit model origin ctx) index,
      ((priorCode.seq (body index)).execute environment Reference initial).effectWeight
          (fun record => effects record.1) ≤
        ratio * (priorCode.execute environment Reference initial).effectWeight
          (fun record => effects record.1))
    (priorCode : Circuit model origin ctx) :
    ((priorCode.seq (forRange count body)).execute environment Reference initial).effectWeight
        (fun record => effects record.1) ≤
      ratio ^ count * (priorCode.execute environment Reference initial).effectWeight
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
