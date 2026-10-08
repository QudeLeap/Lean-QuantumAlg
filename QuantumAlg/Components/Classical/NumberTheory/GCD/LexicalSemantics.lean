/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.LayoutSemantics
import all QuantumAlg.Components.Classical.NumberTheory.GCD.ScheduledSemantics

/-!
# Exact GCD execution through the three lexical state cells

The store transformation follows the actual three allocations, initialized
Euclidean schedule and matching releases. Its internal separation facts are
consequences of those allocations. The result-zero premise is discharged by
the enclosing retained allocation, rather than required of caller storage.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Enter the three actual scopes, execute the schedule and release exactly those cells. -/
def lexicalStep (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (lexicalBody (model := model) input result).Path :=
  let final := scheduledStep (model := model) (underLoop input width) (currentCell ctx width)
    (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
    (pushLoopStore width store)
  (popLoopStore width final.1, final.2)

/-- All three lexical scopes compose on the original complete quantum-reference register. -/
theorem gcdLexical_execute (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (lexicalBody (model := model) input result).execute Reference state =
      state.mapClassical (fun entry =>
        let result := lexicalStep (model := model) input result entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let scheduled := scheduledBody (model := model) (underLoop input width) (currentCell ctx width)
    (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
  let scheduledUpdate := scheduledStep (model := model) (underLoop input width) (currentCell ctx
    width)
    (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
  let inner := Circuit.workspace (previousCtx ctx width)
    (previousCtx ctx width).canonicalFreshKey .bit
    (previousCtx ctx width).canonicalFreshKey_fresh scheduled
  let innerUpdate := fun store : Store (previousCtx ctx width) =>
    let next := scheduledUpdate (store.pushWorkspace
      (previousCtx ctx width).canonicalFreshKey .bit
      (previousCtx ctx width).canonicalFreshKey_fresh)
    (Store.popWorkspace (previousCtx ctx width).canonicalFreshKey .bit
      (previousCtx ctx width).canonicalFreshKey_fresh next.1, next.2)
  let middle := Circuit.workspace (currentCtx ctx width)
    (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (currentCtx ctx width).canonicalFreshKey_fresh inner
  let middleUpdate := fun store : Store (currentCtx ctx width) =>
    let next := innerUpdate (store.pushWorkspace
      (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (currentCtx ctx width).canonicalFreshKey_fresh)
    (Store.popWorkspace (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (currentCtx ctx width).canonicalFreshKey_fresh next.1, next.2)
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh middle
    (fun before => let next := middleUpdate before.1; ((next.1, before.2), next.2))
    (fun reference {_} _ initial => ?_) Reference state).trans ?_
  · exact Circuit.execute_workspace_mapClassical (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh inner
      (fun before => let next := innerUpdate before.1; ((next.1, before.2), next.2))
      (fun reference {_} _ initial =>
        Circuit.execute_workspace_mapClassical (previousCtx ctx width).canonicalFreshKey
          .bit (previousCtx ctx width).canonicalFreshKey_fresh scheduled
          (fun before => let next := scheduledUpdate before.1; ((next.1, before.2), next.2))
          (fun reference history _ state =>
            (gcdScheduled_execute (model := model) (underLoop input width) (currentCell ctx width)
              (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
              reference state).trans (ExecutionState.executionState_mapClassical_congr _ rfl))
          reference initial)
      reference initial
  · congr 1

/-- The automatically separated lexical state returns the original operands' exact GCD word. -/
theorem gcdLexical_read_result (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (zeroValue : (store.read (cellRead result)).toNat = 0) :
    ((lexicalStep (model := model) input result store).1).read (cellRead result) =
      encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
        (decodeOperands (store.read input))) := by
  have separated := gcdLayout_state_separation ctx width
  have inputSeparated := gcdLayout_input_separation input width
  have resultSeparated := gcdLayout_input_separation (cellRead result) width
  have resultKeys : (underLoop (cellRead result) width).storageKeys =
      [(writeUnderLoop result width).key] := rfl
  have firstResult : (currentCell ctx width).key ≠ (writeUnderLoop result width).key := by
    simpa only [resultKeys, List.mem_singleton] using resultSeparated.1
  have secondResult : (previousCell ctx width).key ≠ (writeUnderLoop result width).key := by
    simpa only [resultKeys, List.mem_singleton] using resultSeparated.2.1
  have activeResult : (conditionCell ctx width).key ≠ (writeUnderLoop result width).key := by
    simpa only [resultKeys, List.mem_singleton] using resultSeparated.2.2
  have initializedZero : ((pushLoopStore width store).read
      (cellRead (writeUnderLoop result width))).toNat = 0 :=
    (congrArg CShape.Value.toNat (gcdLayout_push_read (cellRead result) width store)).trans
      zeroValue
  have actual := gcdScheduled_read_result (underLoop input width) (currentCell ctx width)
    (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
    separated.1 separated.2.1 separated.2.2 inputSeparated.1
    firstResult secondResult activeResult (pushLoopStore width store) initializedZero
  have exited := gcdLayout_pop_read (cellRead result) width
    (scheduledStep (model := model) (underLoop input width) (currentCell ctx width) (previousCell
      ctx width)
      (conditionCell ctx width) (writeUnderLoop result width) (pushLoopStore width store)).1
  exact exited.trans (actual.trans (congrArg
    (fun value => encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
      (decodeOperands value))) (gcdLayout_push_read input width store)))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
