/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Reduction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution

/-!
# Real stored-order and early-factor branch execution

The dependent path records below follow only the arms selected by the actual
stored guard and sampler flags. Their complete CQ equations compose the same
guard, modular-power and GCD circuits; no source outcome or mathematical
selector replaces a branch of the actual interpreter.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- Record only the actual reduction or absent-option arm of the stored guard. -/
def checkedArmStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx ×
      (if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output)).Path
  | .bit false, store => BitWord.instructionStep (execution := model) (packOutputOp cells output)
      store
  | .bit true, store => reduceStep (model := model) source cells output store

/-- Select the genuine guard branch with the actual bit read from its incoming store. -/
def guardChoiceStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).Path :=
  let value := store.read (activeRead cells)
  let selected := checkedArmStep (model := model) source cells output value store
  (selected.1, ⟨value, selected.2⟩)

/-- The five actual guard writes precede their actual stored-bit branch. -/
def checkedStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (checkedOrder (model := model) source cells output).Path :=
  let guarded := guardStep (model := model) cells store
  let selected := guardChoiceStep (model := model) source cells output guarded.1
  (selected.1, (guarded.2, selected.2))

private theorem guard_path_execute (cells : Cells ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (guardOrder (model := model) cells).execute Reference state =
      state.mapClassical (fun entry => ((guardStep (model := model) cells entry.1).1,
        (entry.2.1, (entry.2.2, (guardStep (model := model) cells entry.1).2)))) := by
  exact guard_execute cells Reference state

private theorem guardChoice_execute (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).execute
            Reference state =
      state.mapClassical (fun entry => ((guardChoiceStep (model := model) source cells output
          entry.1).1,
        (entry.2.1, (entry.2.2, (guardChoiceStep (model := model) source cells output
            entry.1).2)))) := by
  refine (Circuit.execute_branch_mapClassical (activeRead cells)
    (fun value => if value.toBool then reduce (model := model) source cells output
      else BitWord.instruction (execution := model) (packOutputOp cells output))
    (fun value entry =>
      let actual := checkedArmStep (model := model) source cells output value entry.1
      ((actual.1, entry.2), actual.2)) ?_ Reference state).trans ?_
  · intro value reference history _ initial
    cases value with
    | bit value =>
      cases value
      · exact BitWord.bitWord_instruction_execute (packOutputOp cells output) initial
      · exact reduce_execute source cells output reference initial
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual guard and reduction branch preserve every full quantum-reference block. -/
theorem checked_execute (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (checkedOrder (model := model) source cells output).execute Reference state =
      state.mapClassical (fun entry => ((checkedStep (model := model) source cells output
          entry.1).1,
        (entry.2.1, (entry.2.2, (checkedStep (model := model) source cells output entry.1).2))))
            := by
  unfold checkedOrder
  rw [Circuit.execute_seq, guardChoice_execute, guard_path_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Record the actual early-factor pack or the actual order-guard suffix. -/
def dispatchArmStep (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx ×
      (if value.toBool then BitWord.instruction (execution := model) (packEarlyOp parameter output)
        else checkedOrder (model := model) source cells output).Path
  | .bit false, store => checkedStep (model := model) source cells output store
  | .bit true, store => BitWord.instructionStep (execution := model) (packEarlyOp parameter
      output) store

/-- Read the real sampler flag and preserve the path of its actually selected branch. -/
def dispatchStep (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) : Store ctx × (dispatch (model := model) source parameter cells
        output).Path :=
  let value := store.read (.first (.second parameter))
  let selected := dispatchArmStep (model := model) source parameter cells output value store
  (selected.1, ⟨value, selected.2⟩)

/-- The real sampler flag selects the original priority branch on full CQ blocks. -/
theorem dispatch_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (dispatch (model := model) source parameter cells output).execute Reference state =
      state.mapClassical (fun entry => ((dispatchStep (model := model) source parameter cells
          output entry.1).1,
        (entry.2.1, (entry.2.2, (dispatchStep (model := model) source parameter cells output
            entry.1).2)))) := by
  refine (Circuit.execute_branch_mapClassical (.first (.second parameter))
    (fun value => if value.toBool then
      BitWord.instruction (execution := model) (packEarlyOp parameter output)
      else checkedOrder (model := model) source cells output)
    (fun value entry =>
      let actual := dispatchArmStep (model := model) source parameter cells output value entry.1
      ((actual.1, entry.2), actual.2)) ?_ Reference state).trans ?_
  · intro value reference history _ initial
    cases value with
    | bit value =>
      cases value
      · exact checked_execute source cells output reference initial
      · exact BitWord.bitWord_instruction_execute (packEarlyOp parameter output) initial
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
