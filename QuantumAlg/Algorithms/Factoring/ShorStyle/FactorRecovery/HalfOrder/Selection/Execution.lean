/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Packing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Execution

/-!
# Actual left-priority GCD selection records

Each record below is the deterministic store and path of the existing real
instructions. The stored left comparison controls the actual branch: the
right GCD runs only in the rejecting arm. The equalities preserve complete
quantum-reference density blocks throughout that same execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The real comparison record is followed by actual option packaging. -/
def checkedPackStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (FactorRange.code (model := model) (checkRefs cells)) (pack (model :=
        model) cells output)).Path :=
  let checked := FactorRange.executionStep (model := model) (checkRefs cells) store
  let next := packStep (model := model) cells output checked.1
  (next.1, (checked.2, next.2))

/-- The right arm records its real GCD, actual comparisons and actual final writes. -/
def rightStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (right (model := model) halfPower cells output).Path :=
  let reduced := NativeHalfGCD.step (model := model) true halfPower cells.candidate store
  let next := checkedPackStep (model := model) cells output reduced.1
  (next.1, (reduced.2, next.2))

/-- The selected branch records only the instructions that really execute. -/
def chooseArmStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx ×
      (if value.toBool then pack (model := model) cells output else right (model := model)
          halfPower cells output).Path
  | .bit false, store => rightStep (model := model) halfPower cells output store
  | .bit true, store => packStep (model := model) cells output store

/-- Read the real left decision and retain the selected path in the actual branch record. -/
def chooseStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (choose (model := model) halfPower cells output).Path :=
  let value := store.read (.storage cells.lower.toCStorageRef)
  let next := chooseArmStep (model := model) halfPower cells output value store
  (next.1, ⟨value, next.2⟩)

/-- The actual first comparison feeds its real stored bit into the left-priority branch. -/
def checkedChooseStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) : Store ctx ×
      (Circuit.seq (FactorRange.code (model := model) (checkRefs cells))
        (choose (model := model) halfPower cells output)).Path :=
  let checked := FactorRange.executionStep (model := model) (checkRefs cells) store
  let next := chooseStep (model := model) halfPower cells output checked.1
  (next.1, (checked.2, next.2))

/-- The complete factor-selection record begins with its actual left GCD call. -/
def step (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code (model := model) halfPower cells output).Path :=
  let reduced := NativeHalfGCD.step (model := model) false halfPower cells.candidate store
  let next := checkedChooseStep (model := model) halfPower cells output reduced.1
  (next.1, (reduced.2, next.2))

private lemma checkedPack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (FactorRange.code (model := model) (checkRefs cells)) (pack (model := model)
        cells output)).execute environment Reference state =
      state.mapClassical (fun entry => ((checkedPackStep (model := model) cells output entry.1).1,
        (entry.2.1, (entry.2.2, (checkedPackStep (model := model) cells output entry.1).2)))) := by
  rw [Circuit.execute_seq, pack_execute, FactorRange.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma right_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (right (model := model) halfPower cells output).execute environment Reference state =
      state.mapClassical (fun entry => ((rightStep (model := model) halfPower cells output
          entry.1).1,
        (entry.2.1, (entry.2.2, (rightStep (model := model) halfPower cells output entry.1).2))))
            := by
  unfold right
  rw [Circuit.execute_seq, checkedPack_execute, NativeHalfGCD.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma chooseArm_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (if value.toBool then pack (model := model) cells output else right (model := model) halfPower
        cells output).execute environment Reference state =
      state.mapClassical (fun entry => ((chooseArmStep (model := model) halfPower cells output
          value entry.1).1,
        (entry.2.1, (entry.2.2, (chooseArmStep (model := model) halfPower cells output value
            entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · exact right_execute halfPower cells output Reference state
      · exact pack_execute cells output Reference state

private lemma choose_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (choose (model := model) halfPower cells output).execute environment Reference state =
      state.mapClassical (fun entry => ((chooseStep (model := model) halfPower cells output
          entry.1).1,
        (entry.2.1, (entry.2.2, (chooseStep (model := model) halfPower cells output entry.1).2))))
            := by
  refine (Circuit.execute_branch_mapClassical
    (environment := environment) (.storage cells.lower.toCStorageRef)
    (fun value => if value.toBool then pack (model := model) cells output
      else right (model := model) halfPower cells output)
    (fun value entry =>
      let actual := chooseArmStep (model := model) halfPower cells output value entry.1
      ((actual.1, entry.2), actual.2))
    (chooseArm_execute (model := model) halfPower cells output) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma checkedChoose_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (FactorRange.code (model := model) (checkRefs cells))
        (choose (model := model) halfPower cells output)).execute environment Reference state =
      state.mapClassical (fun entry => ((checkedChooseStep (model := model) halfPower cells output
          entry.1).1,
        (entry.2.1, (entry.2.2, (checkedChooseStep (model := model) halfPower cells output
            entry.1).2)))) := by
  rw [Circuit.execute_seq, choose_execute, FactorRange.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The real left-priority circuit executes exactly its actual store and path on full CQ blocks. -/
lemma code_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) halfPower cells output).execute environment Reference state =
      state.mapClassical (fun entry => ((step (model := model) halfPower cells output entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) halfPower cells output entry.1).2)))) := by
  unfold code
  rw [Circuit.execute_seq, checkedChoose_execute, NativeHalfGCD.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
