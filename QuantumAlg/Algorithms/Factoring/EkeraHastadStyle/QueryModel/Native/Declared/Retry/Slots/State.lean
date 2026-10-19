/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Slots
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual declared EH selector allocation

The three paid retentions initialize the first-success flag and word before
any source draw. The complete caller, hidden-service, and external-reference
state survives these real allocations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Slots

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma retain_pair_execute {model : ExecutionModel}
    {environment : model.Environment} (ctx : RuntimeCtx model.kind)
    (firstKey : StorageKey) (firstShape : CShape) (firstFresh : firstKey ∉ ctx.keys)
    (secondKey : StorageKey) (secondShape : CShape)
    (secondFresh : secondKey ∉ (ctx.addRetained firstKey firstShape firstFresh).keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (Circuit.retain (model := model) ctx firstKey firstShape firstFresh)
      (Circuit.retain (ctx.addRetained firstKey firstShape firstFresh)
        secondKey secondShape secondFresh)).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((entry.1.pushRetained firstKey firstShape firstFresh).pushRetained
          secondKey secondShape secondFresh, (entry.2.1, (entry.2.2, ((), ()))))) := by
  simp only [Circuit.execute_seq, Circuit.execute_retain, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private lemma retain_triple_execute {model : ExecutionModel}
    {environment : model.Environment} (ctx : RuntimeCtx model.kind)
    (firstKey : StorageKey) (firstShape : CShape) (firstFresh : firstKey ∉ ctx.keys)
    (secondKey : StorageKey) (secondShape : CShape)
    (secondFresh : secondKey ∉ (ctx.addRetained firstKey firstShape firstFresh).keys)
    (thirdKey : StorageKey) (thirdShape : CShape)
    (thirdFresh : thirdKey ∉
      ((ctx.addRetained firstKey firstShape firstFresh).addRetained
        secondKey secondShape secondFresh).keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (Circuit.retain (model := model) ctx firstKey firstShape firstFresh)
      (Circuit.seq (Circuit.retain (ctx.addRetained firstKey firstShape firstFresh)
        secondKey secondShape secondFresh)
        (Circuit.retain ((ctx.addRetained firstKey firstShape firstFresh).addRetained
          secondKey secondShape secondFresh) thirdKey thirdShape thirdFresh))).execute
          environment Reference state =
      state.mapClassical (fun entry =>
        ((((entry.1.pushRetained firstKey firstShape firstFresh).pushRetained
          secondKey secondShape secondFresh).pushRetained thirdKey thirdShape thirdFresh),
          (entry.2.1, (entry.2.2, ((), ((), ())))))) := by
  rw [Circuit.execute_seq, Circuit.execute_retain, retain_pair_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)

/-- Actual store after the three selector retentions. -/
def pushStore (store : Store ctx) : Store (Native.Retry.Slots.context ctx width) :=
  ((store.pushRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).pushRetained
    (Native.Retry.Slots.acceptedContext ctx).canonicalFreshKey (.unsignedWord width)
    (Native.Retry.Slots.acceptedContext ctx).canonicalFreshKey_fresh).pushRetained
      (Native.Retry.Slots.selectedContext ctx width).canonicalFreshKey
      (.product .bit (.unsignedWord width))
      (Native.Retry.Slots.selectedContext ctx width).canonicalFreshKey_fresh

/-- Structural access to an earlier caller value beneath the three cells. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (Native.Retry.Slots.context ctx width) shape :=
  ((input.underRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underRetained
    (Native.Retry.Slots.acceptedContext ctx).canonicalFreshKey (.unsignedWord width)
    (Native.Retry.Slots.acceptedContext ctx).canonicalFreshKey_fresh).underRetained
      (Native.Retry.Slots.selectedContext ctx width).canonicalFreshKey
      (.product .bit (.unsignedWord width))
      (Native.Retry.Slots.selectedContext ctx width).canonicalFreshKey_fresh

/-- Retention preserves every caller and service history in the same reference block. -/
lemma allocate_execute {model : ExecutionModel}
    {environment : model.Environment} (ctx : RuntimeCtx model.kind)
    (width : Nat) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Native.Retry.Slots.allocate (model := model) ctx width).execute environment Reference state =
      state.mapClassical (fun entry =>
        (pushStore ctx width entry.1,
          (entry.2.1, (entry.2.2, ((), ((), ())))))) := by
  exact retain_triple_execute ctx
    ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (Native.Retry.Slots.acceptedContext ctx).canonicalFreshKey (.unsignedWord width)
    (Native.Retry.Slots.acceptedContext ctx).canonicalFreshKey_fresh
    (Native.Retry.Slots.selectedContext ctx width).canonicalFreshKey
    (.product .bit (.unsignedWord width))
    (Native.Retry.Slots.selectedContext ctx width).canonicalFreshKey_fresh
    Reference state

/-- Initial flag and selected word have their actual default values. -/
lemma initial (store : Store ctx) :
    (pushStore ctx width store).read
      (.storage (Native.Retry.Slots.acceptedRef ctx width).toCStorageRef) = .bit false ∧
    (pushStore ctx width store).read
      (.storage (Native.Retry.Slots.selectedRef ctx width).toCStorageRef) =
        CShape.initialValue (.unsignedWord width) := by
  constructor <;> rfl

/-- Every earlier caller read remains exactly equal after the real retentions. -/
lemma read (store : Store ctx) {shape : CShape} (input : CInputRef ctx shape) :
    (pushStore ctx width store).read (liftInput ctx width input) = store.read input := by
  exact (Store.read_pushRetained_underRetained _ _ _ _ _).trans
    ((Store.read_pushRetained_underRetained _ _ _ _ _).trans
      (Store.read_pushRetained_underRetained _ _ _ _ _))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Slots
