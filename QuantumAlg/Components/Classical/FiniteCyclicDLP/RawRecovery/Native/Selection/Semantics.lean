/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Native.Semantics

/-!
# Exact status selection through the real optional-result pack

Failure skips recovery and writes the actual optional-none representation.
Success retains the exact original recovery/check payload. All claims concern
the supplied actual status and inverse words; upstream checked inversion is
not replaced by a mathematical inverse assumption or a host computation.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution Modular.NativePower NormalizedRecovery.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The selected actual branch preserves every complete quantum-reference block. -/
theorem selectedRecoveryChoice_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectedRecoveryChoice (model := model) input modulus payload value).execute Reference state =
      state.mapClassical (fun entry =>
        let result := selectedRecoveryChoiceStep (model := model) input modulus payload value
            entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit value =>
      cases value
      · simp only [selectedRecoveryChoice, selectedRecoveryChoiceStep, CShape.Value.toBool]
        refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · exact (withRecovery_execute input modulus payload Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The actual branch and final materialization compose with their true store and path. -/
theorem selectedRecoveryBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (selectedRecoveryBody (model := model) input modulus success payload output).execute
        Reference state =
      state.mapClassical (fun entry =>
        let result := selectedRecoveryBodyStep (model := model) input modulus success payload
            output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (.branch success (selectedRecoveryChoice (model := model) input modulus payload))
    (BitWord.instruction (execution := model) (selectedRecoveryPackOp success payload output))
    (fun before =>
      let value := before.1.read success
      let chosen := selectedRecoveryChoiceStep (model := model) input modulus payload value before.1
      ((chosen.1, before.2), ⟨value, chosen.2⟩))
    (fun before =>
      let packed := BitWord.instructionStep (execution := model)
        (selectedRecoveryPackOp success payload output) before.1
      ((packed.1, before.2), packed.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    refine (Circuit.execute_branch_mapClassical success _
      (fun value before =>
        let result := selectedRecoveryChoiceStep (model := model) input modulus payload value
            before.1
        ((result.1, before.2), result.2)) ?_ reference initial).trans ?_
    · intro value reference history _ initial
      exact (selectedRecoveryChoice_execute input modulus payload value reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
    · exact ExecutionState.executionState_mapClassical_congr _ rfl
  · intro reference history _ initial
    exact (BitWord.bitWord_instruction_execute (execution := model)
      (selectedRecoveryPackOp success payload output) initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual chosen branch changes at most its payload cell. -/
theorem selectedRecoveryChoice_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width)) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape) (separate : payload.key ∉ other.storageKeys)
    (store : Store ctx) :
    (selectedRecoveryChoiceStep (model := model) input modulus payload value store).1.read other =
      store.read other := by
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact withRecovery_read_other input modulus payload other separate store

/-- The unplaced suffix preserves all structural reads outside payload and optional-result keys. -/
theorem selectedRecoveryBody_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) {shape : CShape} (other : CInputRef ctx shape)
    (payloadFree : payload.key ∉ other.storageKeys) (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (selectedRecoveryBodyStep (model := model) input modulus success payload output
        store).1.read other =
      store.read other := by
  unfold selectedRecoveryBodyStep
  dsimp only [BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (selectedRecoveryPackOp success payload output) other outputFree]
  exact selectedRecoveryChoice_read_other input modulus payload _ other payloadFree store

/-- Actual optional packing returns none or the genuine computed payload according to status. -/
theorem selectedRecoveryBody_result {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) (statusFree : payload.key ∉ success.storageKeys)
    (store : Store ctx) :
    (selectedRecoveryBodyStep (model := model) input modulus success payload output
        store).1.read (wordRead output) =
      if (store.read success).toBool then .optionSome
        (recoveryValue (store.read (.first input)) (store.read (.first (.second input)))
          (store.read (.second (.second input))) (store.read modulus)) else .optionNone := by
  let chosen := selectedRecoveryChoiceStep (model := model) input modulus payload (store.read
      success) store
  have statusValue : chosen.1.read success = store.read success :=
    selectedRecoveryChoice_read_other input modulus payload _ success statusFree store
  have packed : (chosen.1.applyOp (selectedRecoveryPackOp success payload output)).read
      (wordRead output) = CShape.packOption
        (.product (chosen.1.read success) (chosen.1.read (wordRead payload))) :=
    Store.read_applyOp_output chosen.1 (selectedRecoveryPackOp success payload output)
  change (chosen.1.applyOp (selectedRecoveryPackOp success payload output)).read
    (wordRead output) = _
  rw [packed, statusValue]
  dsimp only [chosen]
  cases status : store.read success with
  | bit value =>
      cases value
      · rfl
      · simp only [CShape.Value.toBool, if_true, CShape.packOption_true,
          selectedRecoveryChoiceStep]
        exact congrArg CShape.Value.optionSome (withRecovery_value input modulus payload store)

private theorem selectionPayload_free {shape : CShape} (input : CInputRef ctx shape) :
    (selectionPayloadCell ctx width).key ∉ (underSelection input width).storageKeys := by
  rw [underSelection, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

/-- Actual payload allocation, branch, pack and release preserve full quantum-reference data. -/
theorem withSelectedRecovery_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withSelectedRecovery (model := model) input modulus success output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := withSelectedRecoveryStep (model := model) input modulus success output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh
    (selectedRecoveryPlaced (model := model) input modulus success output)
    (fun before =>
      let result := selectedRecoveryBodyStep (model := model)
        (underSelection input width) (underSelection modulus width)
        (underSelection success width) (selectionPayloadCell ctx width)
        (writeUnderSelection output width) before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (selectedRecoveryBody_execute (underSelection input width) (underSelection modulus width)
      (underSelection success width) (selectionPayloadCell ctx width)
      (writeUnderSelection output width) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The result uses original status and words, with no caller scratch or output promise. -/
theorem withSelectedRecovery_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    (withSelectedRecoveryStep (model := model) input modulus success output store).1.read
        (wordRead output) =
      if (store.read success).toBool then .optionSome
        (recoveryValue (store.read (.first input)) (store.read (.first (.second input)))
          (store.read (.second (.second input))) (store.read modulus)) else .optionNone := by
  unfold withSelectedRecoveryStep
  rw [Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh _ (wordRead output)]
  change (selectedRecoveryBodyStep (model := model) _ _ _ _ _ _).1.read
    (wordRead (writeUnderSelection output width)) = _
  rw [selectedRecoveryBody_result _ _ _ _ _ (selectionPayload_free success)]
  let entered := store.pushWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh
  let lifted := input.underWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh
  have leftRead : entered.read (.first lifted) = store.read (.first input) :=
    Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh (.first input)
  have rightRead : entered.read (.first (.second lifted)) =
      store.read (.first (.second input)) :=
    Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh (.first (.second input))
  have inverseRead : entered.read (.second (.second lifted)) =
      store.read (.second (.second input)) :=
    Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh (.second (.second input))
  simp only [underSelection, Store.read_pushWorkspace_underWorkspace]
  rw [leftRead, rightRead, inverseRead]

/-- Only the original optional-result cell may change after the payload is released. -/
theorem withSelectedRecovery_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (withSelectedRecoveryStep (model := model) input modulus success output store).1.read other =
      store.read other := by
  unfold withSelectedRecoveryStep
  rw [Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh _ other]
  change (selectedRecoveryBodyStep (model := model) _ _ _ _ _ _).1.read (underSelection other
      width) = _
  rw [selectedRecoveryBody_read_other _ _ _ _ _ _ (selectionPayload_free other)]
  · exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other
  · change output.key ∉ (underSelection other width).storageKeys
    simpa only [underSelection, CInputRef.storageKeys_underWorkspace] using separate

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
