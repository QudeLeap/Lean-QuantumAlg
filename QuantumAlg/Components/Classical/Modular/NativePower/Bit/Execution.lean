/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Circuit
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopedLaws

/-!
# Same-store execution of selected modular multiplications

The square's actual output store determines the exponent bit read by the
following branch. These concrete records contain that value and only the
selected path; their equations are derived from the existing interpreter.
Every complete quantum-reference density block is preserved throughout.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The real update and branch path selected by a stored Boolean. -/
def multiplyChoiceStep (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (store : Store ctx) :
    Store ctx × (multiplyChoice (model := model) base modulus output value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => scopedMultiplyStep (model := model) (wordRead output) base modulus output store

private lemma multiplyChoice_execute (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (multiplyChoice (model := model) base modulus output value).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := multiplyChoiceStep (model := model) base modulus output value entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · refine (Circuit.execute_id_mapClassical
          (environment := environment) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · refine (nativePower_scopedMultiply_execute (wordRead output) base modulus output
          Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual square store supplies the following branch's concrete exponent bit. -/
def bitStep (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (store : Store ctx) : Store ctx × (bitCircuit (model := model) base modulus output bit).Path :=
  let squared := scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
    modulus output store
  let value := squared.1.read bit
  let selected := multiplyChoiceStep (model := model) base modulus output value squared.1
  (selected.1, (squared.2, ⟨value, selected.2⟩))

/-- Actual square-and-multiply execution records exactly its same-store classical selection. -/
lemma nativePower_bit_execute (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (bitCircuit (model := model) base modulus output bit).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := bitStep (model := model) base modulus output bit entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (scopedMultiply (model := model) (wordRead output) (wordRead output) modulus output)
    (.branch bit (multiplyChoice (model := model) base modulus output))
    (fun before =>
      let result := scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
        modulus output before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let value := before.1.read bit
      let result := multiplyChoiceStep (model := model) base modulus output value before.1
      ((result.1, before.2), ⟨value, result.2⟩))
    ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (nativePower_scopedMultiply_execute (wordRead output) (wordRead output)
      modulus output reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    refine (Circuit.execute_branch_mapClassical (environment := environment) bit _
      (fun value before =>
        let result := multiplyChoiceStep (model := model) base modulus output value before.1
        ((result.1, before.2), result.2)) ?_ reference initial).trans ?_
    · intro value reference history _ initial
      exact (multiplyChoice_execute base modulus output value reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
    · exact ExecutionState.executionState_mapClassical_congr _ rfl
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Concrete records for the finite composition of exponent-bit circuits. -/
def foldStep (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (bits : List (CInputRef ctx .bit)) → Store ctx →
      Store ctx × (foldBits (model := model) base modulus output bits).Path
  | [], store => (store, ())
  | bit :: rest, store =>
      let first := bitStep (model := model) base modulus output bit store
      let later := foldStep base modulus output rest first.1
      (later.1, (first.2, later.2))

/-- Every finite exponent prefix is interpreted by the same actual store/path composition. -/
lemma nativePower_fold_execute (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (foldBits (model := model) base modulus output bits).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := foldStep (model := model) base modulus output bits entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction bits generalizing Reference History with
  | nil =>
      exact (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons bit rest ih =>
      refine (Circuit.execute_seq_mapClassical (environment := environment)
        (bitCircuit (model := model) base modulus output bit)
        (foldBits (model := model) base modulus output rest)
        (fun before =>
          let result := bitStep (model := model) base modulus output bit before.1
          ((result.1, before.2), result.2))
        (fun before =>
          let result := foldStep (model := model) base modulus output rest before.1
          ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
      · intro reference history _ initial
        exact (nativePower_bit_execute base modulus output bit reference initial).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · intro reference history _ initial
        exact (ih reference initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
      · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
