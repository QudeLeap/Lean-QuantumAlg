/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.GuardedRemainder
import all QuantumAlg.Components.Classical.NumberTheory.GCD.RemainderSemantics

/-!
# Establishing the Euclidean state from actual operand cells

Two copies and the actual comparison/negation pair initialize the stored
state. The only zero used here is the retained result's allocation value;
the lexical state words and active bit may have arbitrary previous contents.
The internal placement facts are independent of all operand values.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Concrete store produced by the four real initialization operations. -/
def initializationStore (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) : Store ctx :=
  (((store.applyOp (.wordUnary .copy width ctx (.first input) first)).applyOp
    (.wordUnary .copy width ctx (.second input) second)).applyOp
      (testActiveOp first zero active)).applyOp (negateActiveOp active)

/-- Initialization preserves complete quantum-reference blocks and records its four real steps. -/
theorem gcdInitialization_execute (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (initializationBody input first second zero active).execute Reference state =
      state.mapClassical (fun entry =>
        (initializationStore input first second zero active entry.1,
          (entry.2, ((), ((), ((), ())))))) := by
  simp only [initializationBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- No initialization operation changes a structural read outside the three written cells. -/
theorem gcdInitialization_read_other (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    {observed : CShape} (other : CInputRef ctx observed)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (store : Store ctx) :
    (initializationStore input first second zero active store).read other = store.read other := by
  unfold initializationStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (negateActiveOp active) other activeFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (testActiveOp first zero active) other activeFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.wordUnary .copy width ctx (.second input) second) other secondFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.wordUnary .copy width ctx (.first input) first) other firstFree]

/-- The initialized machine words are the exact original operands, and the loop bit is correct. -/
theorem gcdInitialization_store_values (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstInput : first.key ∉ input.storageKeys)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (store : Store ctx)
    (zeroValue : (store.read zero).toNat = 0) :
    let final := initializationStore input first second zero active store
    final.read (cellRead first) = (store.read input).first ∧
      final.read (cellRead second) = (store.read input).second ∧
      storedEuclidReady first zero active final := by
  let leftCopy : ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
    .wordUnary .copy width ctx (.first input) first
  let rightCopy : ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
    .wordUnary .copy width ctx (.second input) second
  let leftStore := store.applyOp leftCopy
  let bothStore := leftStore.applyOp rightCopy
  let tested := bothStore.applyOp (testActiveOp first zero active)
  have leftValue : leftStore.read (cellRead first) = (store.read input).first :=
    Store.read_applyOp_output store leftCopy
  have leftInput : leftStore.read input = store.read input :=
    Store.read_applyOp_of_not_mem_storageKeys store leftCopy input firstInput
  have bothFirst : bothStore.read (cellRead first) = (store.read input).first := by
    rw [op_preserves_cell rightCopy first (Ne.symm firstSecond) leftStore, leftValue]
  have bothSecond : bothStore.read (cellRead second) = (store.read input).second := by
    have actual := Store.read_applyOp_output leftStore rightCopy
    change bothStore.read (cellRead second) = (leftStore.read input).second at actual
    rw [leftInput] at actual
    exact actual
  have bothZero : bothStore.read zero = store.read zero := by
    rw [Store.read_applyOp_of_not_mem_storageKeys leftStore rightCopy zero secondZero,
      Store.read_applyOp_of_not_mem_storageKeys store leftCopy zero firstZero]
  have finalFirst : (initializationStore input first second zero active store).read
      (cellRead first) = (store.read input).first := by
    change (tested.applyOp (negateActiveOp active)).read (cellRead first) = _
    rw [op_preserves_cell (negateActiveOp active) first activeFirst tested,
      op_preserves_cell (testActiveOp first zero active) first activeFirst bothStore, bothFirst]
  have finalSecond : (initializationStore input first second zero active store).read
      (cellRead second) = (store.read input).second := by
    change (tested.applyOp (negateActiveOp active)).read (cellRead second) = _
    rw [op_preserves_cell (negateActiveOp active) second activeSecond tested,
      op_preserves_cell (testActiveOp first zero active) second activeSecond bothStore, bothSecond]
  refine ⟨finalFirst, finalSecond, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat
      (gcdInitialization_read_other input first second zero active zero
        firstZero secondZero activeZero store)).trans zeroValue
  · change ((tested.applyOp (negateActiveOp active)).read (cellRead active)).toBool = _
    rw [negate_read, test_read first zero active bothStore, bothFirst, bothZero,
      finalFirst, zeroValue]
    simp

/-- The internally initialized state is exactly the pure GCD input state. -/
theorem gcdInitialization_initialState (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstInput : first.key ∉ input.storageKeys)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (store : Store ctx)
    (zeroValue : (store.read zero).toNat = 0) :
    storedEuclidState first second (initializationStore input first second zero active store) =
      ClassicalAlgorithms.NumberTheory.GCD.initialState
        (decodeOperands (store.read input)) := by
  have actual := gcdInitialization_store_values input first second zero active
    firstSecond activeFirst activeSecond firstInput firstZero secondZero activeZero store zeroValue
  unfold storedEuclidState
  rw [actual.1, actual.2.1]
  cases value : store.read input with
  | product left right =>
      cases left
      cases right
      rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
