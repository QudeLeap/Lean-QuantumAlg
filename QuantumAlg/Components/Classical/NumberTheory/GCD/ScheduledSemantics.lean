/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.InitializationSemantics
import all QuantumAlg.Components.Classical.NumberTheory.GCD.LoopSemantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Exact result of the initialized Euclidean instruction schedule

The complete state equation composes actual initialization, the selected
iteration paths and the final copy. The inner zero premise is the allocation
value of the retained result, established outside the lexical scopes. Under
the automatically placed cells, the copied result is the existing total GCD
evaluator for every intrinsically bounded operand pair.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution
open ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual initialized iteration followed by the final native word-copy store update. -/
def scheduledStep (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx × (scheduledBody (model := model) input first second active
      result).Path :=
  let initial := initializationStep (model := model) input first second (cellRead result) active
    store
  let iterated := iteratedRemainderStep (model := model) first second (cellRead result) active
    (Euclid.gcdFuel width) initial.1
  let copied := BitWord.instructionStep (execution := model)
    (.wordUnary .copy width ctx (cellRead second) result) iterated.1
  (copied.1, (initial.2, (iterated.2, copied.2)))

/-- Initialization, iteration and final copy compose on every complete quantum-reference block. -/
lemma gcdScheduled_execute (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scheduledBody (model := model) input first second active result).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := scheduledStep (model := model) input first second active result entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let zero := cellRead result
  let init := initializationBody (model := model) input first second zero active
  let loop := Circuit.iterate (Euclid.gcdFuel width)
    (guardedRemainder (model := model) first second zero active)
  let copy : ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
    .wordUnary .copy width ctx (cellRead second) result
  let copyCircuit := BitWord.instruction (execution := model) copy
  let initRecord := fun before : Store ctx × model.HiddenState =>
    let next := initializationStep (model := model) input first second zero active before.1
    ((next.1, before.2), next.2)
  let loopRecord := fun before : Store ctx × model.HiddenState =>
    let next := iteratedRemainderStep (model := model) first second zero active
      (Euclid.gcdFuel width) before.1
    ((next.1, before.2), next.2)
  let copyRecord := fun before : Store ctx × model.HiddenState =>
    let next := BitWord.instructionStep (execution := model) copy before.1
    ((next.1, before.2), next.2)
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) init (.seq loop copyCircuit) initRecord
    (Circuit.sequenceRecord loop copyCircuit loopRecord copyRecord) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (gcdInitialization_execute (model := model)
      input first second zero active reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact Circuit.execute_sequenceRecord
      (environment := environment) loop copyCircuit loopRecord copyRecord
      (by
        intro reference history _ state
        exact (gcdLoop_execute (model := model)
          first second zero active (Euclid.gcdFuel width) reference state).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl))
      (by
        intro reference history _ state
        exact (BitWord.bitWord_instruction_execute
          (environment := environment) (execution := model) copy state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)) reference initial
  · exact ExecutionState.executionState_mapClassical_congr _ rfl


/-- The final actual copy returns the exact total GCD word of the original encoded operands. -/
lemma gcdScheduled_read_result (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstInput : first.key ∉ input.storageKeys)
    (firstResult : first.key ≠ result.key) (secondResult : second.key ≠ result.key)
    (activeResult : active.key ≠ result.key) (store : Store ctx)
    (zeroValue : (store.read (cellRead result)).toNat = 0) :
    ((scheduledStep (model := model) input first second active result store).1).read (cellRead
      result) =
      encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
        (decodeOperands (store.read input))) := by
  let zero := cellRead result
  have firstZero : first.key ∉ zero.storageKeys := by
    simpa only [zero, cellRead, CInputRef.storageKeys, List.mem_singleton] using firstResult
  have secondZero : second.key ∉ zero.storageKeys := by
    simpa only [zero, cellRead, CInputRef.storageKeys, List.mem_singleton] using secondResult
  have activeZero : active.key ∉ zero.storageKeys := by
    simpa only [zero, cellRead, CInputRef.storageKeys, List.mem_singleton] using activeResult
  let initial := initializationStore input first second zero active store
  let iterated := iteratedRemainderStep (model := model) first second zero active (Euclid.gcdFuel
    width) initial
  have initialized := gcdInitialization_store_values input first second zero active
    firstSecond activeFirst activeSecond firstInput firstZero secondZero activeZero store zeroValue
  have initialState := gcdInitialization_initialState input first second zero active
    firstSecond activeFirst activeSecond firstInput firstZero secondZero activeZero store zeroValue
  have loopState := gcdLoop_state first second zero active firstSecond activeFirst activeSecond
    firstZero secondZero activeZero (Euclid.gcdFuel width) initial initialized.2.2
  rw [initialState] at loopState
  have previousValue := congrArg Euclid.State.second loopState
  have pureResult := ClassicalAlgorithms.NumberTheory.GCD.gcdFinalState_result_eq_eval
    (decodeOperands (store.read input))
  have copied : ((scheduledStep (model := model) input first second active result store).1).read
      (cellRead result) = iterated.1.read (cellRead second) :=
    Store.read_applyOp_output iterated.1
      (.wordUnary .copy width ctx (cellRead second) result)
  have natural : (((scheduledStep (model := model) input first second active result store).1).read
      (cellRead result)).toNat =
      (ClassicalAlgorithms.NumberTheory.GCD.eval
        (decodeOperands (store.read input))).val :=
    (congrArg CShape.Value.toNat copied).trans (previousValue.trans pureResult)
  cases value : ((scheduledStep (model := model) input first second active result store).1).read
      (cellRead result) with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      simpa only [value, CShape.Value.toNat] using natural

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
