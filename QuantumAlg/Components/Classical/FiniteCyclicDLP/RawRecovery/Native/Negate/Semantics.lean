/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Negate
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model

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

private theorem negateChoice_execute (modulus right zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (negateChoice modulus right zero output value).execute Reference state =
      state.mapClassical (fun entry =>
        ((negateChoiceStep modulus right zero output value entry.1).1,
          (entry.2, (negateChoiceStep modulus right zero output value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [negateChoice, CShape.Value.toBool, negateChoiceStep]
        refine (Circuit.execute_classical_mapClassical
          (negateSubtractOp modulus right output) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [negateChoice, CShape.Value.toBool, negateChoiceStep]
        refine (Circuit.execute_classical_mapClassical
          (negateCopyOp zero output) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _

/-- Actual equality and selected instruction compose on every complete quantum-reference block. -/
theorem negateBody_execute (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (negateBody modulus right zero flag output).execute Reference state =
      state.mapClassical (fun entry =>
        ((negateBodyStep modulus right zero flag output entry.1).1,
          (entry.2, (negateBodyStep modulus right zero flag output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (negateEqualOp right zero flag))
    (.branch (negateRead flag) (negateChoice modulus right zero output))
    (fun store => (store.applyOp (negateEqualOp right zero flag), ()))
    (fun store =>
      ((negateChoiceStep modulus right zero output (store.read (negateRead flag)) store).1,
        ⟨store.read (negateRead flag),
          (negateChoiceStep modulus right zero output (store.read (negateRead flag)) store).2⟩))
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical (negateEqualOp right zero flag)
        reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => Circuit.execute_branch_mapClassical (negateRead flag) _
      (negateChoiceStep modulus right zero output)
      (negateChoice_execute modulus right zero output) reference initial)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem negateBodyStep_store (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (negateBodyStep modulus right zero flag output store).1 =
      let checked := store.applyOp (negateEqualOp right zero flag)
      if (checked.read (negateRead flag)).toBool then checked.applyOp (negateCopyOp zero output)
        else checked.applyOp (negateSubtractOp modulus right output) := by
  dsimp only [negateBodyStep]
  cases chosen : (store.applyOp (negateEqualOp right zero flag)).read (negateRead flag) with
  | bit bit => cases bit <;> rfl

/-- The body writes the exact selected copy or wrapping subtraction on its original reads. -/
theorem negateBody_result (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width))
    (modulusFree : flag.key ∉ modulus.storageKeys) (rightFree : flag.key ∉ right.storageKeys)
    (zeroFree : flag.key ∉ zero.storageKeys) (store : Store ctx) :
    (negateBodyStep modulus right zero flag output store).1.read (negateRead output) =
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
  rw [negateBodyStep_store]
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
theorem negateBody_read_other (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (flagFree : flag.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys) :
    (negateBodyStep modulus right zero flag output store).1.read other = store.read other := by
  have checked := Store.read_applyOp_of_not_mem_storageKeys store
    (negateEqualOp right zero flag) other flagFree
  rw [negateBodyStep_store]
  dsimp only
  split
  · exact (Store.read_applyOp_of_not_mem_storageKeys _
      (negateCopyOp zero output) other outputFree).trans checked
  · exact (Store.read_applyOp_of_not_mem_storageKeys _
      (negateSubtractOp modulus right output) other outputFree).trans checked

private def negateFlagScope (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (negateZeroCtx ctx width) (negateZeroCtx ctx width) :=
  .workspace (negateZeroCtx ctx width) (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh (negatePlaced modulus right output)

private def negateFlagStep (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (negateZeroCtx ctx width)) :
    Store (negateZeroCtx ctx width) × (negateFlagScope modulus right output).Path :=
  let result := negateBodyStep (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width)
    (store.pushWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh result.1, result.2)

private theorem negateFlagScope_execute (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (negateZeroCtx ctx width) Reference History) :
    (negateFlagScope modulus right output).execute Reference state =
      state.mapClassical (fun entry =>
        ((negateFlagStep modulus right output entry.1).1,
          (entry.2, (negateFlagStep modulus right output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh (negatePlaced modulus right output)
    (negateBodyStep (underNegate modulus width) (underNegate right width)
      (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
      (writeUnderNegate output width))
    (negateBody_execute (underNegate modulus width) (underNegate right width)
      (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
      (writeUnderNegate output width)) Reference state).trans ?_
  congr 1

/-- The complete actual branch and both releases retain every quantum-reference block and path. -/
theorem withNegate_execute (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (withNegate modulus right output).execute Reference state = state.mapClassical (fun entry =>
      ((withNegateStep modulus right output entry.1).1,
        (entry.2, (withNegateStep modulus right output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (negateFlagScope modulus right output)
    (negateFlagStep modulus right output) (negateFlagScope_execute modulus right output)
    Reference state).trans ?_
  congr 1

/-- Both real allocations preserve every original structural read. -/
theorem enterNegate_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (enterNegate store width).read (underNegate input width) = store.read input := by
  simp only [enterNegate, underNegate, Store.read_pushWorkspace_underWorkspace]

/-- Both matching releases expose exactly the original structural input reference. -/
theorem leaveNegate_read (store : Store (negateCtx ctx width)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (leaveNegate store).read input = store.read (underNegate input width) := by
  simp only [leaveNegate, underNegate, Store.read_popWorkspace_underWorkspace]

private theorem negateFlag_free {shape : CShape} (input : CInputRef ctx shape) :
    (negateFlagCell ctx width).key ∉ (underNegate input width).storageKeys := by
  unfold underNegate
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => (negateZeroCtx ctx width).canonicalFreshKey_fresh
    ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

private theorem negateFlag_zero_separate :
    (negateFlagCell ctx width).key ∉ (negateRead (negateZeroCell ctx width)).storageKeys := by
  change (negateZeroCtx ctx width).canonicalFreshKey ∉ [ctx.canonicalFreshKey]
  intro present
  apply (negateZeroCtx ctx width).canonicalFreshKey_fresh
  rw [List.mem_singleton.mp present]
  exact List.mem_cons_self

/-- The original zero word is initialized by its actual lexical allocation. -/
theorem enterNegate_zero_value (store : Store ctx) (width : Nat) :
    ((enterNegate store width).read (negateRead (negateZeroCell ctx width))).toNat = 0 := by
  have entered := Store.read_pushWorkspace_underWorkspace
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
    (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh
    (.storage (CStorageRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh))
  exact (congrArg CShape.Value.toNat entered).trans rfl

/-- Releasing both scratch cells leaves every original non-output structural read unchanged. -/
theorem withNegate_read_other (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) :
    (withNegateStep modulus right output store).1.read other = store.read other := by
  have result := negateBody_read_other (underNegate modulus width) (underNegate right width)
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
theorem withNegate_value (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((withNegateStep modulus right output store).1.read (negateRead output)).toNat =
      negateNatural width (store.read modulus).toNat (store.read right).toNat := by
  have result := negateBody_result (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width) (negateFlag_free modulus) (negateFlag_free right)
    negateFlag_zero_separate (enterNegate store width)
  have value : ((negateBodyStep (underNegate modulus width) (underNegate right width)
      (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
      (writeUnderNegate output width) (enterNegate store width)).1.read
        (negateRead (writeUnderNegate output width))).toNat =
      negateNatural width (store.read modulus).toNat (store.read right).toNat := by
    simpa only [apply_ite CShape.Value.toNat, enterNegate_read, enterNegate_zero_value,
      CShape.wordSub, CShape.wordOfNat_val, CShape.wordModulus, negateNatural] using
      congrArg CShape.Value.toNat result
  exact (congrArg CShape.Value.toNat (leaveNegate_read _ (negateRead output))).trans value

/-- The original capacity-equality modulus is included by its actual narrowed word value. -/
theorem negateNatural_original (spec : ModulusSpec width) (modulus right : Nat)
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
theorem withNegate_original_value (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus % 2 ^ width)
    (canonical : (store.read right).toNat < spec.modulus) :
    ((withNegateStep modulus right output store).1.read (negateRead output)).toNat =
      (spec.modulus - (store.read right).toNat) % spec.modulus :=
  (withNegate_value modulus right output store).trans
    (negateNatural_original spec _ _ orderValue canonical)

/-- Actual original normalized input yields precisely the pure recovery model's right negation. -/
theorem withNegate_negateRight (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width)
    (input : NormalizedInput spec) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus % 2 ^ width)
    (rightValue : (store.read right).toNat = input.right.val) :
    ((withNegateStep modulus right output store).1.read (negateRead output)).toNat =
      (negateRight spec input).val := by
  have result := withNegate_original_value modulus right output spec store orderValue
    (rightValue ▸ input.right.isLt)
  exact result.trans (congrArg (fun value => (spec.modulus - value) % spec.modulus) rightValue)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
