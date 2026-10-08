/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Records

/-!
# Complete execution of the actual initialized half-factor body

The two real constant-loading circuits compose with the actual left-priority
factor circuit. The resulting equality retains the full store, genuine path
and arbitrary external reference blocks of that same execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private theorem one_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (ConstantWord.circuit (model := model) (oneRef ctx N) 1).execute Reference state =
      state.mapClassical (fun entry => ((oneStep (model := model) entry.1).1, (entry.2.1,
          (entry.2.2, (oneStep (model := model) entry.1).2)))) := by
  refine (ConstantWord.constantWord_fold_execute (model := model) (oneRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) 1)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem modulus_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (ConstantWord.circuit (model := model) (modulusRef ctx N) N).execute Reference state =
      state.mapClassical (fun entry =>
        ((modulusStep (model := model) entry.1).1, (entry.2.1, (entry.2.2, (modulusStep (model :=
            model) entry.1).2)))) := by
  refine (ConstantWord.constantWord_fold_execute (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem modulusTail_execute
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (Circuit.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N)
        (NativeHalfFactor.code (model := model) (liftInput halfPower) (cells ctx N) (liftWrite
            output))).execute
        Reference state =
      state.mapClassical (fun entry => ((modulusTailStep (model := model) halfPower output
          entry.1).1,
        (entry.2.1, (entry.2.2, (modulusTailStep (model := model) halfPower output entry.1).2))))
            := by
  rw [Circuit.execute_seq, NativeHalfFactor.code_execute, modulus_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual initialized body executes its exact physical store and complete path on CQ blocks. -/
theorem body_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((bodyStep (model := model) halfPower output entry.1).1,
        (entry.2.1, (entry.2.2, (bodyStep (model := model) halfPower output entry.1).2)))) := by
  unfold body
  rw [Circuit.execute_seq, modulusTail_execute, one_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
