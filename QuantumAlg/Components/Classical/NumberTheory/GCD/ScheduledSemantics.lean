/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.InitializationSemantics
import all QuantumAlg.Components.Classical.NumberTheory.GCD.LoopSemantics

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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual initialized iteration followed by the final native word-copy store update. -/
def scheduledStep (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx × (scheduledBody input first second active result).Path :=
  let initial := initializationStore input first second (cellRead result) active store
  let iterated := iteratedRemainderStep first second (cellRead result) active
    (Euclid.gcdFuel width) initial
  (iterated.1.applyOp (.wordUnary .copy width ctx (cellRead second) result),
    (((), ((), ((), ()))), (iterated.2, ())))

/-- Initialization, iteration and final copy compose on every complete quantum-reference block. -/
theorem gcdScheduled_execute (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scheduledBody input first second active result).execute Reference state =
      state.mapClassical (fun entry =>
        ((scheduledStep input first second active result entry.1).1,
          (entry.2, (scheduledStep input first second active result entry.1).2))) := by
  let zero := cellRead result
  let body := guardedRemainder first second zero active
  let loop := Circuit.iterate (Euclid.gcdFuel width) body
  let loopStep := iteratedRemainderStep first second zero active (Euclid.gcdFuel width)
  let copy : ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
    .wordUnary .copy width ctx (cellRead second) result
  refine (Circuit.execute_seq_mapClassical
    (initializationBody input first second zero active) (.seq loop (.classical copy))
    (fun store => (initializationStore input first second zero active store,
      ((), ((), ((), ())))))
    (fun store => ((loopStep store).1.applyOp copy, ((loopStep store).2, ())))
    (fun reference {_} _ initial => by
      refine (gcdInitialization_execute input first second zero active reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_seq_mapClassical loop (.classical copy) loopStep
        (fun store => (store.applyOp copy, ()))
        (gcdLoop_execute first second zero active (Euclid.gcdFuel width))
        (fun reference {_} _ initial => by
          refine (Circuit.execute_classical_mapClassical copy reference initial).trans ?_
          congr 1
          exact Subsingleton.elim _ _)
        reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The final actual copy returns the exact total GCD word of the original encoded operands. -/
theorem gcdScheduled_read_result (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstInput : first.key ∉ input.storageKeys)
    (firstResult : first.key ≠ result.key) (secondResult : second.key ≠ result.key)
    (activeResult : active.key ≠ result.key) (store : Store ctx)
    (zeroValue : (store.read (cellRead result)).toNat = 0) :
    ((scheduledStep input first second active result store).1).read (cellRead result) =
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
  let iterated := iteratedRemainderStep first second zero active (Euclid.gcdFuel width) initial
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
  have copied : ((scheduledStep input first second active result store).1).read
      (cellRead result) = iterated.1.read (cellRead second) :=
    Store.read_applyOp_output iterated.1
      (.wordUnary .copy width ctx (cellRead second) result)
  have natural : (((scheduledStep input first second active result store).1).read
      (cellRead result)).toNat =
      (ClassicalAlgorithms.NumberTheory.GCD.eval
        (decodeOperands (store.read input))).val :=
    (congrArg CShape.Value.toNat copied).trans (previousValue.trans pureResult)
  cases value : ((scheduledStep input first second active result store).1).read
      (cellRead result) with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      simpa only [value, CShape.Value.toNat] using natural

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
