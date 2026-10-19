/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Negate
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Exact actual modular negation through its zero-test branch

The zero word and flag are internal allocations. Original outputs may have
arbitrary values and may coincide with original input storage. The modulus
word represents the original modulus modulo the word capacity, preserving
the boundary where the mathematical modulus equals that capacity.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma negateChoice_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (negateChoice (model := model) modulus right zero output value).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := negateChoiceStep (model := model) modulus right zero output value entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [negateChoice, CShape.Value.toBool, negateChoiceStep]
        exact BitWord.bitWord_instruction_execute (environment := environment)
          (execution := model)
          (negateSubtractOp modulus right output) state
      · simp only [negateChoice, CShape.Value.toBool, negateChoiceStep]
        exact BitWord.bitWord_instruction_execute (environment := environment)
          (execution := model)
          (negateCopyOp zero output) state

/-- Equality and its selected native instruction preserve the complete service/reference record. -/
lemma negateBody_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (negateBody (model := model) modulus right zero flag output).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := negateBodyStep (model := model) modulus right zero flag output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model) (negateEqualOp right zero flag))
    (.branch (negateRead flag) (negateChoice (model := model) modulus right zero output))
    (fun before =>
      let result := BitWord.instructionStep (execution := model) (negateEqualOp right zero flag)
        before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let choice := before.1.read (negateRead flag)
      let result := negateChoiceStep (model := model) modulus right zero output choice before.1
      ((result.1, before.2), ⟨choice, result.2⟩)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (BitWord.bitWord_instruction_execute (environment := environment)
      (execution := model)
      (negateEqualOp right zero flag) initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    refine (Circuit.execute_branch_mapClassical (environment := environment) (negateRead flag) _
      (fun value before =>
        let result := negateChoiceStep (model := model) modulus right zero output value before.1
        ((result.1, before.2), result.2)) ?_ reference initial).trans ?_
    · intro value reference history _ initial
      exact (negateChoice_execute (model := model) modulus right zero output value
        reference initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
    · exact ExecutionState.executionState_mapClassical_congr _ rfl
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma negateBodyStep_store {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (negateBodyStep (model := model) modulus right zero flag output store).1 =
      let checked := store.applyOp (negateEqualOp right zero flag)
      if (checked.read (negateRead flag)).toBool then checked.applyOp (negateCopyOp zero output)
        else checked.applyOp (negateSubtractOp modulus right output) := by
  change (negateChoiceStep (model := model) modulus right zero output
    ((store.applyOp (negateEqualOp right zero flag)).read (negateRead flag))
    (store.applyOp (negateEqualOp right zero flag))).1 = _
  cases chosen : (store.applyOp (negateEqualOp right zero flag)).read (negateRead flag) with
  | bit bit =>
      dsimp only
      rw [chosen]
      cases bit <;> rfl

/-- The body writes the exact selected copy or wrapping subtraction on its original reads. -/
lemma negateBody_result {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width))
    (modulusFree : flag.key ∉ modulus.storageKeys) (rightFree : flag.key ∉ right.storageKeys)
    (zeroFree : flag.key ∉ zero.storageKeys) (store : Store ctx) :
    (negateBodyStep (model := model) modulus right zero flag output store).1.read
      (negateRead output) =
      if (store.read right).toNat = (store.read zero).toNat then store.read zero
        else CShape.wordSub width (store.read modulus) (store.read right) := by
  let checked := store.applyOp (negateEqualOp right zero flag)
  have chosen : checked.read (negateRead flag) =
      .bit (decide ((store.read right).toNat = (store.read zero).toNat)) :=
    Store.read_applyOp_output store (negateEqualOp right zero flag)
  have oldZero : checked.read zero = store.read zero :=
    Store.read_applyOp_of_not_mem_storageKeys store (negateEqualOp right zero flag) zero zeroFree
  have oldRight : checked.read right = store.read right :=
    Store.read_applyOp_of_not_mem_storageKeys store (negateEqualOp right zero flag) right rightFree
  have oldModulus : checked.read modulus = store.read modulus :=
    Store.read_applyOp_of_not_mem_storageKeys store (negateEqualOp right zero flag)
      modulus modulusFree
  rw [negateBodyStep_store (model := model)]
  change (if (checked.read (negateRead flag)).toBool then
    checked.applyOp (negateCopyOp zero output) else
    checked.applyOp (negateSubtractOp modulus right output)).read (negateRead output) = _
  rw [chosen]
  by_cases same : (store.read right).toNat = (store.read zero).toNat
  · simp only [same, decide_true, CShape.Value.toBool, if_true]
    exact (Store.read_applyOp_output checked (negateCopyOp zero output)).trans oldZero
  · simp only [same, decide_false, CShape.Value.toBool, Bool.false_eq_true, if_false]
    exact (Store.read_applyOp_output checked (negateSubtractOp modulus right output)).trans
      (congrArg₂ (CShape.wordSub width) oldModulus oldRight)

/-- Both actual writes preserve every structural read outside the flag and output keys. -/
lemma negateBody_read_other {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (flagFree : flag.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys) :
    (negateBodyStep (model := model) modulus right zero flag output store).1.read other =
      store.read other := by
  have checked := Store.read_applyOp_of_not_mem_storageKeys store
    (negateEqualOp right zero flag) other flagFree
  rw [negateBodyStep_store (model := model)]
  dsimp only
  split
  · exact (Store.read_applyOp_of_not_mem_storageKeys _
      (negateCopyOp zero output) other outputFree).trans checked
  · exact (Store.read_applyOp_of_not_mem_storageKeys _
      (negateSubtractOp modulus right output) other outputFree).trans checked

private def negateFlagScope {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (negateZeroCtx ctx width) (negateZeroCtx ctx width) :=
  .workspace (negateZeroCtx ctx width) (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh
      (negatePlaced (model := model) modulus right output)

private def negateFlagStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (negateZeroCtx ctx width)) :
    Store (negateZeroCtx ctx width) ×
      (negateFlagScope (model := model) modulus right output).Path :=
  let result := negateBodyStep (model := model)
    (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width)
    (store.pushWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh result.1, result.2)

private lemma negateFlagScope_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (negateZeroCtx ctx width) Reference (model.HiddenState × History)) :
    (negateFlagScope (model := model) modulus right output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := negateFlagStep (model := model) modulus right output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh
    (negatePlaced (model := model) modulus right output)
    (fun before =>
      let result := negateBodyStep (model := model)
        (underNegate modulus width) (underNegate right width)
        (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
        (writeUnderNegate output width) before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (negateBody_execute (model := model)
    (underNegate modulus width) (underNegate right width)
      (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
      (writeUnderNegate output width) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both releases preserve the selected native path and complete hidden/reference state. -/
lemma withNegate_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withNegate (model := model) modulus right output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := withNegateStep (model := model) modulus right output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (negateFlagScope (model := model) modulus right output)
    (fun before =>
      let result := negateFlagStep (model := model) modulus right output before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (negateFlagScope_execute (model := model) modulus right output reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both real allocations preserve every original structural read. -/
lemma enterNegate_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (enterNegate store width).read (underNegate input width) = store.read input := by
  simp only [enterNegate, underNegate, Store.read_pushWorkspace_underWorkspace]

/-- Both matching releases expose exactly the original structural input reference. -/
lemma leaveNegate_read (store : Store (negateCtx ctx width)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (leaveNegate store).read input = store.read (underNegate input width) := by
  simp only [leaveNegate, underNegate, Store.read_popWorkspace_underWorkspace]

private lemma negateFlag_free {shape : CShape} (input : CInputRef ctx shape) :
    (negateFlagCell ctx width).key ∉ (underNegate input width).storageKeys := by
  unfold underNegate
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => (negateZeroCtx ctx width).canonicalFreshKey_fresh
    ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

private lemma negateFlag_zero_separate :
    (negateFlagCell ctx width).key ∉ (negateRead (negateZeroCell ctx width)).storageKeys := by
  change (negateZeroCtx ctx width).canonicalFreshKey ∉ [ctx.canonicalFreshKey]
  intro present
  apply (negateZeroCtx ctx width).canonicalFreshKey_fresh
  rw [List.mem_singleton.mp present]
  exact List.mem_cons_self

/-- The original zero word is initialized by its actual lexical allocation. -/
lemma enterNegate_zero_value (store : Store ctx) (width : Nat) :
    ((enterNegate store width).read (negateRead (negateZeroCell ctx width))).toNat = 0 := by
  have entered := Store.read_pushWorkspace_underWorkspace
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
    (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh
    (.storage (CStorageRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh))
  exact (congrArg CShape.Value.toNat entered).trans rfl

/-- Releasing both scratch cells leaves every original non-output structural read unchanged. -/
lemma withNegate_read_other {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) :
    (withNegateStep (model := model) modulus right output store).1.read other =
      store.read other := by
  have result := negateBody_read_other (model := model)
    (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width) (enterNegate store width) (underNegate other width)
    (negateFlag_free other) (by
      change output.key ∉ (underNegate other width).storageKeys
      simpa only [underNegate, CInputRef.storageKeys_underWorkspace] using separate)
  exact (leaveNegate_read _ other).trans (result.trans (enterNegate_read store other width))

/-- Natural projection of the original zero-copy or wrapping-subtraction branch. -/
def negateNatural (width modulus right : Nat) : Nat :=
  if right = 0 then 0 else (modulus + 2 ^ width - right) % 2 ^ width

/-- The actual complete branch has this exact arithmetic value on original caller reads. -/
lemma withNegate_value {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((withNegateStep (model := model) modulus right output store).1.read
      (negateRead output)).toNat =
      negateNatural width (store.read modulus).toNat (store.read right).toNat := by
  have result := negateBody_result (model := model)
    (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width) (negateFlag_free modulus) (negateFlag_free right)
    negateFlag_zero_separate (enterNegate store width)
  have value : ((negateBodyStep (model := model)
    (underNegate modulus width) (underNegate right width)
      (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
      (writeUnderNegate output width) (enterNegate store width)).1.read
        (negateRead (writeUnderNegate output width))).toNat =
      negateNatural width (store.read modulus).toNat (store.read right).toNat := by
    simpa only [apply_ite CShape.Value.toNat, enterNegate_read, enterNegate_zero_value,
      CShape.wordSub, CShape.wordOfNat_val, CShape.wordModulus, negateNatural] using
      congrArg CShape.Value.toNat result
  exact (congrArg CShape.Value.toNat (leaveNegate_read _ (negateRead output))).trans value

/-- The original capacity-equality modulus is included by its actual narrowed word value. -/
lemma negateNatural_original (spec : ModulusSpec width) (modulus right : Nat)
    (orderValue : modulus = spec.modulus % 2 ^ width) (canonical : right < spec.modulus) :
    negateNatural width modulus right = (spec.modulus - right) % spec.modulus := by
  by_cases zero : right = 0
  · simp only [negateNatural, zero, if_true, Nat.sub_zero, Nat.mod_self]
  · have positive : 0 < right := Nat.pos_of_ne_zero zero
    have fits : spec.modulus ≤ 2 ^ width := spec.le_capacity
    have difference : spec.modulus - right < spec.modulus := by omega
    have differenceFits : spec.modulus - right < 2 ^ width := by omega
    rw [negateNatural, if_neg zero, orderValue, Nat.mod_eq_of_lt difference]
    by_cases boundary : spec.modulus = 2 ^ width
    · rw [boundary, Nat.mod_self, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    · have orderFits : spec.modulus < 2 ^ width := by omega
      rw [Nat.mod_eq_of_lt orderFits]
      have subtract : spec.modulus + 2 ^ width - right =
          (spec.modulus - right) + 2 ^ width := by omega
      rw [subtract, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt differenceFits]

/-- The original modular negation is computed for every fitted modulus, including capacity. -/
lemma withNegate_original_value {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus % 2 ^ width)
    (canonical : (store.read right).toNat < spec.modulus) :
    ((withNegateStep (model := model) modulus right output store).1.read
      (negateRead output)).toNat =
      (spec.modulus - (store.read right).toNat) % spec.modulus :=
  (withNegate_value (model := model) modulus right output store).trans
    (negateNatural_original spec _ _ orderValue canonical)

/-- Actual original normalized input yields precisely the pure recovery model's right negation. -/
lemma withNegate_negateRight {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width)
    (input : NormalizedInput spec) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus % 2 ^ width)
    (rightValue : (store.read right).toNat = input.right.val) :
    ((withNegateStep (model := model) modulus right output store).1.read
      (negateRead output)).toNat =
      (negateRight spec input).val := by
  have result := withNegate_original_value (model := model) modulus right output spec store
    orderValue
    (rightValue ▸ input.right.isLt)
  exact result.trans (congrArg (fun value => (spec.modulus - value) % spec.modulus) rightValue)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
