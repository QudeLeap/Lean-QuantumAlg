/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Validation
import all QuantumAlg.Components.Classical.GF2.Native.Decision.Semantics

/-!
# Complete actual records of original sample validation

The real instruction sequence reads the current store at every sample and
candidate bit. Actual parity outcomes control the original failure updates.
Both lexical bits are initialized and popped, with every caller-store,
reference and history correlation preserved and no input-state premise.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private theorem operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (BitWord.instruction (execution := model) op).execute Reference state =
      state.mapClassical (fun entry =>
        let result := BitWord.instructionStep (execution := model) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_instruction_execute (execution := model) op state

omit [BitWord.Selected model] in
private theorem idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.id (model := model) ctx).execute Reference state =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  exact (Circuit.execute_id_mapClassical (model := model) Reference state).trans
    (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The actual product write precedes the actual parity update. -/
def validationColumnStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (validationColumn input candidate parity product row column).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model)
      (validationProductOp input candidate product row column))
    (BitWord.instruction (execution := model) (validationParityOp parity product))
    (BitWord.instructionStep (execution := model)
      (validationProductOp input candidate product row column))
    (BitWord.instructionStep (execution := model) (validationParityOp parity product)) store

/-- Each actual AND and XOR preserves the complete state/reference/history interpretation. -/
theorem gf2ValidationColumn_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (validationColumn (model := model) input candidate parity product row column).execute
        Reference state =
      state.mapClassical (fun entry =>
        ((validationColumnStep input candidate parity product row column entry.1).1,
          (entry.2.1, (entry.2.2,
            (validationColumnStep input candidate parity product row column entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (operation_execute (validationProductOp input candidate product row column))
    (operation_execute (validationParityOp parity product)) Reference state

/-- The actual row starts with clear, then columns, then the current stored parity branch. -/
def validationRowBodyStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount) (store : Store ctx) :
    Store ctx × (validationRowBody input candidate success parity product row).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (pivotClearOp parity))
    (.seq (Circuit.forRange width
        (validationColumn (model := model) input candidate parity product row))
      (.branch (.storage parity.toCStorageRef)
        (decisionChoice (model := model) true success)))
    (BitWord.instructionStep (execution := model) (pivotClearOp parity))
    (Circuit.sequenceStoreRecord
      (Circuit.forRange width
        (validationColumn (model := model) input candidate parity product row))
      (.branch (.storage parity.toCStorageRef)
        (decisionChoice (model := model) true success))
      (Circuit.forRangeStoreRecord width _
        (validationColumnStep (model := model) input candidate parity product row))
      (fun current =>
        let value := current.read (.storage parity.toCStorageRef)
        let actual := decisionChoiceStep true success value current
        (actual.1, ⟨value, actual.2⟩))) store

/-- The original full row body follows the same real finite record for every complete state. -/
theorem gf2ValidationRowBody_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (validationRowBody (model := model) input candidate success parity product row).execute
        Reference state =
      state.mapClassical (fun entry =>
        ((validationRowBodyStep input candidate success parity product row entry.1).1,
          (entry.2.1, (entry.2.2,
            (validationRowBodyStep input candidate success parity product row entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (operation_execute (pivotClearOp parity))
    (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
      (Circuit.execute_forRangeStoreRecord (model := model) width _ _
        (gf2ValidationColumn_execute (model := model) input candidate parity product row))
      (fun reference {_} _ current => Circuit.execute_branchStoreRecord (model := model)
        (.storage parity.toCStorageRef) (decisionChoice (model := model) true success)
        (decisionChoiceStep true success) (decisionChoice_execute (model := model) true success)
        reference current))
    Reference state

/-- The real product cell is pushed and popped around the complete actual row body. -/
def scopedValidationRowStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store (pivotSinkContext ctx)) :
    Store (pivotSinkContext ctx) × (scopedValidationRow input candidate success row).Path :=
  let actual := validationRowBodyStep (validationInput input) (pivotSearchWrite candidate)
    (pivotSearchWrite success) (validationParity ctx) (pivotLatch (pivotSinkContext ctx)) row
    (store.pushWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh)
  (Store.popWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh actual.1, actual.2)

private theorem scopedValidationRow_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (Reference : Register) {History : Type} [Fintype History]
    (state : State (pivotSinkContext ctx) Reference (model.HiddenState × History)) :
    (scopedValidationRow (model := model) input candidate success row).execute Reference state =
      state.mapClassical (fun entry =>
        ((scopedValidationRowStep input candidate success row entry.1).1,
          (entry.2.1, (entry.2.2,
            (scopedValidationRowStep input candidate success row entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (model := model) _ _ _ _ _
    (gf2ValidationRowBody_execute (model := model) _ _ _ _ _ row) Reference state

/-- The actual parity cell encloses the actual product scope and is then released. -/
def validateRowStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) :
    Store ctx × (validateRow input candidate success row).Path :=
  let actual := scopedValidationRowStep input candidate success row
    (store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- Both real row scopes preserve the complete actual store/reference/history transformation. -/
theorem gf2ValidationRow_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (validateRow (model := model) input candidate success row).execute Reference state =
      state.mapClassical (fun entry =>
        ((validateRowStep input candidate success row entry.1).1,
          (entry.2.1, (entry.2.2,
            (validateRowStep input candidate success row entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (model := model) _ _ _ _ _
    (scopedValidationRow_execute (model := model) input candidate success row) Reference state

/-- The current stored success bit selects the real row record or the original identity. -/
def validationRowChoiceStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (validationRowChoice input candidate success row value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => validateRowStep input candidate success row store

private theorem rowChoice_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (validationRowChoice (model := model) input candidate success row value).execute
        Reference state =
      state.mapClassical (fun entry =>
        ((validationRowChoiceStep input candidate success row value entry.1).1,
          (entry.2.1, (entry.2.2,
            (validationRowChoiceStep input candidate success row value entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · exact gf2ValidationRow_execute (model := model) input candidate success row Reference state

/-- Each original row branch records its actual current success value. -/
def validationSampleStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) :
    Store ctx × (validationSample input candidate success row).Path :=
  let value := store.read (.storage success.toCStorageRef)
  let actual := validationRowChoiceStep input candidate success row value store
  (actual.1, ⟨value, actual.2⟩)

/-- The actual current success value controls the complete original row transformation. -/
theorem gf2ValidationSample_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (validationSample (model := model) input candidate success row).execute Reference state =
      state.mapClassical (fun entry =>
        ((validationSampleStep input candidate success row entry.1).1,
          (entry.2.1, (entry.2.2,
            (validationSampleStep input candidate success row entry.1).2)))) :=
  Circuit.execute_branchStoreRecord (model := model) (.storage success.toCStorageRef)
    (validationRowChoice (model := model) input candidate success row)
    (validationRowChoiceStep input candidate success row)
    (rowChoice_execute (model := model) input candidate success row) Reference state

/-- The actual row records always precede the original final success self-AND. -/
def validateSamplesStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (store : Store ctx) : Store ctx × (validateSamples input candidate success).Path :=
  Circuit.sequenceStoreRecord
    (Circuit.forRange rowCount (validationSample (model := model) input candidate success))
    (BitWord.instruction (execution := model) (pivotSelectedOp success))
    (Circuit.forRangeStoreRecord rowCount _
      (validationSampleStep (model := model) input candidate success))
    (BitWord.instructionStep (execution := model) (pivotSelectedOp success)) store

/-- Original row order and the final real marker preserve all complete input correlations. -/
theorem gf2ValidationSamples_execute
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (validateSamples (model := model) input candidate success).execute Reference state =
      state.mapClassical (fun entry =>
        ((validateSamplesStep input candidate success entry.1).1,
          (entry.2.1, (entry.2.2,
            (validateSamplesStep input candidate success entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (Circuit.execute_forRangeStoreRecord (model := model) rowCount _ _
      (gf2ValidationSample_execute (model := model) input candidate success))
    (operation_execute (pivotSelectedOp success)) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
