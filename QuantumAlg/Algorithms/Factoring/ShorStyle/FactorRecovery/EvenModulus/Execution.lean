/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.EvenModulus
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution

/-!
# Complete CQ execution of the original even-modulus exception

The existing native instruction and constant-load execution equations compose
on the actual store. The record preserves all complete quantum-reference
blocks and counts the real flag initialization, payload load and option pack.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private theorem two_execute (cells : Cells ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (ConstantWord.circuit (model := model) cells.halfPower 2).execute Reference state =
      state.mapClassical (fun entry => ((twoStep (model := model) cells entry.1).1,
        (entry.2.1, (entry.2.2, (twoStep (model := model) cells entry.1).2)))) := by
  refine (ConstantWord.constantWord_fold_execute (model := model) cells.halfPower
    (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem twoPack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (ConstantWord.circuit (model := model) cells.halfPower 2)
      (BitWord.instruction (execution := model) (packOutputOp cells output))).execute Reference
          state =
      state.mapClassical (fun entry => ((twoPackStep (model := model) cells output entry.1).1,
        (entry.2.1, (entry.2.2, (twoPackStep (model := model) cells output entry.1).2)))) := by
  rw [Circuit.execute_seq, BitWord.bitWord_instruction_execute, two_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem setTwoPack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (BitWord.instruction (execution := model) (setActiveOp cells))
      (.seq (ConstantWord.circuit (model := model) cells.halfPower 2)
        (BitWord.instruction (execution := model) (packOutputOp cells output)))).execute Reference
            state =
      state.mapClassical (fun entry => ((setTwoPackStep (model := model) cells output entry.1).1,
        (entry.2.1, (entry.2.2, (setTwoPackStep (model := model) cells output entry.1).2)))) := by
  rw [Circuit.execute_seq, twoPack_execute, BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The real even-modulus branch has its exact complete store and genuine instruction record. -/
theorem even_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (evenModulus (model := model) cells output).execute Reference state =
      state.mapClassical (fun entry => ((evenStep (model := model) cells output entry.1).1,
        (entry.2.1, (entry.2.2, (evenStep (model := model) cells output entry.1).2)))) := by
  unfold evenModulus
  rw [Circuit.execute_seq, setTwoPack_execute, BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
