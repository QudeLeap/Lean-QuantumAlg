/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Native

/-!
# Exact normalized recovery on arbitrary caller stores

The actual operations preserve the entire quantum-reference state. Every
scratch separation is discharged by the lexical layout. Original output
values and aliases are unrestricted. The mathematical input inverse is only
a representative read from the actual upstream word, with no validity
premise added by this success component.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual native composition preserves shared state and every quantum-reference block. -/
theorem recoveryBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right inverse : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (candidate reconstruction : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (recoveryBody (model := model) left right inverse modulus candidate reconstruction
      verified output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := recoveryBodyStep (model := model) left right inverse modulus candidate
          reconstruction verified output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [recoveryBody, Circuit.execute_seq, nativePower_scopedMultiply_execute,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The two true native reductions followed by the stored reconstruction check. -/
def recoveryValue (left right inverse : CShape.Word width)
    (modulus : CShape.Word (width + 1)) : CShape.Value (OutputShape width) :=
  let candidate := multiplyValue right inverse modulus
  .product candidate
    (.bit (decide ((multiplyValue candidate left modulus).toNat = right.toNat)))

/-- Only scratch writes preceding a later read require separation in the unplaced body. -/
theorem recoveryBody_result {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right inverse : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (candidate reconstruction : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (candidateLeft : candidate.key ∉ left.storageKeys)
    (candidateRight : candidate.key ∉ right.storageKeys)
    (candidateModulus : candidate.key ∉ modulus.storageKeys)
    (reconstructionRight : reconstruction.key ∉ right.storageKeys)
    (reconstructionCandidate : reconstruction.key ∉ (wordRead candidate).storageKeys)
    (verifiedCandidate : verified.key ∉ (wordRead candidate).storageKeys) (store : Store ctx) :
    (recoveryBodyStep (model := model) left right inverse modulus candidate reconstruction
      verified output store).1.read (wordRead output) =
        recoveryValue (store.read left) (store.read right) (store.read inverse)
          (store.read modulus) := by
  let recovered := (scopedMultiplyStep (model := model) right inverse modulus candidate store).1
  let reconstructed :=
    (scopedMultiplyStep (model := model) (wordRead candidate) left modulus reconstruction
      recovered).1
  let checked := reconstructed.applyOp (recoveryEqualOp right reconstruction verified)
  have candidateValue := nativePower_scopedMultiply_result (model := model) right inverse modulus
    candidate store
  have oldLeft := nativePower_scopedMultiply_read_other (model := model) right inverse modulus
    candidate
    left candidateLeft store
  have oldRight := nativePower_scopedMultiply_read_other (model := model) right inverse modulus
    candidate
    right candidateRight store
  have oldModulus := nativePower_scopedMultiply_read_other (model := model) right inverse modulus
    candidate
    modulus candidateModulus store
  have reconstructedValue := nativePower_scopedMultiply_result (model := model)
    (wordRead candidate) left
    modulus reconstruction recovered
  have savedCandidate := nativePower_scopedMultiply_read_other (model := model)
    (wordRead candidate) left
    modulus reconstruction (wordRead candidate) reconstructionCandidate recovered
  have savedRight := nativePower_scopedMultiply_read_other (model := model)
    (wordRead candidate) left
    modulus reconstruction right reconstructionRight recovered
  have checkedCandidate := Store.read_applyOp_of_not_mem_storageKeys reconstructed
    (recoveryEqualOp right reconstruction verified) (wordRead candidate) verifiedCandidate
  have checkValue : checked.read (wordRead verified) = .bit
      (decide ((reconstructed.read (wordRead reconstruction)).toNat =
        (reconstructed.read right).toNat)) :=
    Store.read_applyOp_output reconstructed (recoveryEqualOp right reconstruction verified)
  change (checked.applyOp (recoveryPackOp candidate verified output)).read (wordRead output) = _
  have packed : (checked.applyOp (recoveryPackOp candidate verified output)).read
      (wordRead output) = .product (checked.read (wordRead candidate))
        (checked.read (wordRead verified)) :=
    Store.read_applyOp_output checked (recoveryPackOp candidate verified output)
  rw [packed, checkedCandidate, savedCandidate, candidateValue, checkValue,
    reconstructedValue, savedRight, oldRight, candidateValue, oldLeft, oldModulus]
  rfl

/-- The unplaced body preserves every structural read outside its four real output keys. -/
theorem recoveryBody_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right inverse : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (candidate reconstruction : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    {shape : CShape} (other : CInputRef ctx shape)
    (candidateFree : candidate.key ∉ other.storageKeys)
    (reconstructionFree : reconstruction.key ∉ other.storageKeys)
    (verifiedFree : verified.key ∉ other.storageKeys) (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (recoveryBodyStep (model := model) left right inverse modulus candidate reconstruction
      verified output store).1.read other =
      store.read other := by
  unfold recoveryBodyStep
  dsimp only [BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (recoveryPackOp candidate verified output) other outputFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (recoveryEqualOp right reconstruction verified) other verifiedFree,
    nativePower_scopedMultiply_read_other (model := model) _ _ _ _ other reconstructionFree,
    nativePower_scopedMultiply_read_other (model := model) _ _ _ _ other candidateFree]

/-- All original reads are preserved on the three actual lexical entries. -/
theorem enterRecovery_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (enterRecovery store width).read (underRecovery input width) = store.read input := by
  simp only [enterRecovery, underRecovery, Store.read_pushWorkspace_underWorkspace]

/-- All three matching releases expose exactly the original caller read. -/
theorem leaveRecovery_read (store : Store (recoveryCtx ctx width)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (leaveRecovery store).read input = store.read (underRecovery input width) := by
  simp only [leaveRecovery, underRecovery, Store.read_popWorkspace_underWorkspace]

private theorem candidate_free {shape : CShape} (input : CInputRef ctx shape) :
    (candidateCell ctx width).key ∉ (underRecovery input width).storageKeys := by
  simp only [underRecovery, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

private theorem reconstruction_free {shape : CShape} (input : CInputRef ctx shape) :
    (reconstructionCell ctx width).key ∉ (underRecovery input width).storageKeys := by
  unfold underRecovery
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
  exact fun present => (candidateCtx ctx width).canonicalFreshKey_fresh
    ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

private theorem verified_free {shape : CShape} (input : CInputRef ctx shape) :
    (verifiedCell ctx width).key ∉ (underRecovery input width).storageKeys := by
  unfold underRecovery
  rw [CInputRef.storageKeys_underWorkspace]
  let lifted := (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh
  exact fun present => (reconstructionCtx ctx width).canonicalFreshKey_fresh
    (lifted.storageKeys_subset_context present)

private theorem reconstruction_candidate_separate :
    (reconstructionCell ctx width).key ∉ (wordRead (candidateCell ctx width)).storageKeys := by
  change (candidateCtx ctx width).canonicalFreshKey ∉ [ctx.canonicalFreshKey]
  intro present
  apply (candidateCtx ctx width).canonicalFreshKey_fresh
  rw [List.mem_singleton.mp present]
  exact List.mem_cons_self

private theorem verified_candidate_separate :
    (verifiedCell ctx width).key ∉ (wordRead (candidateCell ctx width)).storageKeys := by
  change (reconstructionCtx ctx width).canonicalFreshKey ∉ [ctx.canonicalFreshKey]
  intro present
  apply (reconstructionCtx ctx width).canonicalFreshKey_fresh
  rw [List.mem_singleton.mp present]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The complete lexical component depends only on the original four actual input reads. -/
theorem withRecovery_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    (withRecoveryStep (model := model) input modulus output store).1.read (wordRead output) =
      recoveryValue (store.read (.first input)) (store.read (.first (.second input)))
        (store.read (.second (.second input))) (store.read modulus) := by
  unfold withRecoveryStep
  rw [leaveRecovery_read]
  change (recoveryBodyStep (model := model) _ _ _ _ _ _ _ _ _).1.read
    (wordRead (writeUnderRecovery output width)) = _
  rw [recoveryBody_result _ _ _ _ _ _ _ _ (candidate_free _) (candidate_free _)
    (candidate_free _) (reconstruction_free _) reconstruction_candidate_separate
    verified_candidate_separate]
  simp only [enterRecovery_read]

/-- Only the original output cell changes after all real scratch entries are released. -/
theorem withRecovery_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (withRecoveryStep (model := model) input modulus output store).1.read other =
      store.read other := by
  unfold withRecoveryStep
  rw [leaveRecovery_read, recoveryBody_read_other _ _ _ _ _ _ _ _ _
    (candidate_free other) (reconstruction_free other) (verified_free other)]
  · exact enterRecovery_read store other width
  · change output.key ∉ (underRecovery other width).storageKeys
    simpa only [underRecovery, CInputRef.storageKeys_underWorkspace] using separate

/-- The retained pair is the original pure model for any canonical supplied inverse word. -/
theorem withRecovery_original_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (spec : ModulusSpec width)
    (semantic : Input spec) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus)
    (leftValue : (store.read (.first input)).toNat = semantic.leftFrequency.val)
    (rightValue : (store.read (.first (.second input))).toNat = semantic.negatedRightFrequency.val)
    (inverseValue : (store.read (.second (.second input))).toNat = semantic.leftInverse.val) :
    let result := (withRecoveryStep (model := model) input modulus output store).1.read
      (wordRead output)
    result.first.toNat = (outputOf spec semantic).candidate.val ∧
      result.second.toBool = (outputOf spec semantic).verified := by
  dsimp only
  rw [withRecovery_value]
  have positive : 0 < (store.read modulus).toNat := orderValue ▸ modulusSpec_modulus_pos spec
  have fits : (store.read modulus).toNat ≤ 2 ^ width := orderValue ▸ spec.le_capacity
  have candidateValue := nativePower_multiplyValue_toNat
    (store.read (.first (.second input))) (store.read (.second (.second input)))
    (store.read modulus) positive fits
  have reconstructionValue := nativePower_multiplyValue_toNat
    (multiplyValue (store.read (.first (.second input)))
      (store.read (.second (.second input))) (store.read modulus))
    (store.read (.first input)) (store.read modulus) positive fits
  change (multiplyValue _ _ _).toNat = _ ∧
    decide ((multiplyValue _ _ _).toNat = _) = _
  rw [reconstructionValue, candidateValue, orderValue, leftValue, rightValue, inverseValue]
  constructor <;> rfl

/-- Actual allocation, arithmetic and release compose on every full quantum-reference block. -/
theorem withRecovery_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withRecovery (model := model) input modulus output).execute Reference state =
      state.mapClassical (fun entry =>
      let result := withRecoveryStep (model := model) input modulus output entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let inner := recoveryPlaced (model := model) input modulus output
  let innerStep : Store (recoveryCtx ctx width) × model.HiddenState →
      (Store (recoveryCtx ctx width) × model.HiddenState) × inner.Path := fun before =>
    let result := recoveryBodyStep (model := model) (underRecovery (.first input) width)
      (underRecovery (.first (.second input)) width)
      (underRecovery (.second (.second input)) width) (underRecovery modulus width)
      (candidateCell ctx width) (reconstructionCell ctx width) (verifiedCell ctx width)
      (writeUnderRecovery output width) before.1
    ((result.1, before.2), result.2)
  let flag := Circuit.workspace (reconstructionCtx ctx width)
    (reconstructionCtx ctx width).canonicalFreshKey .bit
      (reconstructionCtx ctx width).canonicalFreshKey_fresh inner
  let flagStep : Store (reconstructionCtx ctx width) × model.HiddenState →
      (Store (reconstructionCtx ctx width) × model.HiddenState) × flag.Path := fun before =>
    let result := innerStep (before.1.pushWorkspace (reconstructionCtx ctx width).canonicalFreshKey
      .bit (reconstructionCtx ctx width).canonicalFreshKey_fresh, before.2)
    ((Store.popWorkspace (reconstructionCtx ctx width).canonicalFreshKey .bit
      (reconstructionCtx ctx width).canonicalFreshKey_fresh result.1.1, result.1.2), result.2)
  let middle := Circuit.workspace (candidateCtx ctx width)
    (candidateCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (candidateCtx ctx width).canonicalFreshKey_fresh flag
  let middleStep : Store (candidateCtx ctx width) × model.HiddenState →
      (Store (candidateCtx ctx width) × model.HiddenState) × middle.Path := fun before =>
    let result := flagStep (before.1.pushWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh, before.2)
    ((Store.popWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (candidateCtx ctx width).canonicalFreshKey_fresh result.1.1, result.1.2), result.2)
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh middle middleStep (fun reference {_} _ initial => ?_)
    Reference state).trans ?_
  · refine (Circuit.execute_workspace_mapClassical (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh flag flagStep
      (fun reference' {_} _ initial' => ?_) reference initial).trans ?_
    · refine (Circuit.execute_workspace_mapClassical (reconstructionCtx ctx width).canonicalFreshKey
        .bit (reconstructionCtx ctx width).canonicalFreshKey_fresh inner innerStep
        (fun reference'' {_} _ initial'' => ?_) reference' initial').trans ?_
      · exact (recoveryBody_execute _ _ _ _ _ _ _ _ reference'' initial'').trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · exact ExecutionState.executionState_mapClassical_congr _ rfl
    · exact ExecutionState.executionState_mapClassical_congr _ rfl
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native
