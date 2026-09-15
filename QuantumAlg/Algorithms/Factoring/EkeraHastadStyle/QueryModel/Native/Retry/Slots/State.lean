/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Slots
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Complete state of the real persistent oracle-retry selector allocation

The three retention instructions supply their actual initialized store and
their three actual unit paths. All earlier classical values, history and
quantum-reference density blocks survive unchanged. Freshness establishes
the three distinct selector identities without a caller separation premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Slots

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem mapped_comp {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    {R : Register} (firstDecision : DecidableEq B) (secondDecision : DecidableEq C)
    (state : ExecutionState A R) (first : A → B) (second : B → C) :
    @ExecutionState.mapClassical B C _ _ R secondDecision
        (@ExecutionState.mapClassical A B _ _ R firstDecision state first) second =
      @ExecutionState.mapClassical A C _ _ R secondDecision state (second ∘ first) := by
  let : DecidableEq B := firstDecision
  let : DecidableEq C := secondDecision
  exact ExecutionState.executionState_mapClassical_comp state first second

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)

/-- The real three initialized store extensions, in the program's allocation order. -/
def pushStore (store : Store ctx) : Store (context ctx width) :=
  ((store.pushRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).pushRetained
    (acceptedContext ctx).canonicalFreshKey (.unsignedWord width)
    (acceptedContext ctx).canonicalFreshKey_fresh).pushRetained
      (selectedContext ctx width).canonicalFreshKey (.product .bit (.unsignedWord width))
      (selectedContext ctx width).canonicalFreshKey_fresh

/-- Structural access to an earlier caller value beneath the actual three cells. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (context ctx width) shape :=
  ((input.underRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underRetained
    (acceptedContext ctx).canonicalFreshKey (.unsignedWord width)
    (acceptedContext ctx).canonicalFreshKey_fresh).underRetained
      (selectedContext ctx width).canonicalFreshKey (.product .bit (.unsignedWord width))
      (selectedContext ctx width).canonicalFreshKey_fresh

/-- Actual retention preserves complete states and records every allocation path. -/
theorem nativeOracle_retrySlots_execute (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (allocate ctx width).execute Reference state = state.mapClassical
      (fun entry => (pushStore ctx width entry.1, (entry.2, ((), ((), ()))))) := by
  dsimp only [allocate, Circuit.execute, Execution.interpret, State.retain, State.mapHistory,
    Circuit.Path, context, selectedContext, acceptedContext]
  erw [mapped_comp, mapped_comp, mapped_comp, mapped_comp]
  congr 1
  exact Subsingleton.elim _ _

/-- The real initial accepted flag and selected word are false and the shape's zero value. -/
theorem nativeOracle_retrySlots_initial (store : Store ctx) :
    (pushStore ctx width store).read (.storage (acceptedRef ctx width).toCStorageRef) =
        .bit false ∧
      (pushStore ctx width store).read (.storage (selectedRef ctx width).toCStorageRef) =
        CShape.initialValue (.unsignedWord width) := by
  constructor <;> rfl

/-- Every earlier structural caller read keeps its full actual value. -/
theorem nativeOracle_retrySlots_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) :
    (pushStore ctx width store).read (liftInput ctx width input) = store.read input := by
  exact (Store.read_pushRetained_underRetained _ _ _ _ _).trans
    ((Store.read_pushRetained_underRetained _ _ _ _ _).trans
      (Store.read_pushRetained_underRetained _ _ _ _ _))

private theorem fresh_after {shape : CShape} {inner : RuntimeCtx kind}
    (ref : CWriteRef inner shape) : ref.key ≠ inner.canonicalFreshKey := by
  intro same
  exact inner.canonicalFreshKey_fresh
    (same ▸ MeasurementCells.reference_key_mem ref.toCStorageRef)

/-- The original fresh allocations establish all three real destination inequalities. -/
theorem nativeOracle_retrySlots_keys :
    (acceptedRef ctx width).key ≠ (selectedRef ctx width).key ∧
      (acceptedRef ctx width).key ≠ (unpackedRef ctx width).key ∧
      (selectedRef ctx width).key ≠ (unpackedRef ctx width).key := by
  refine ⟨?_, ?_, ?_⟩
  · exact fresh_after (CWriteRef.retainedHead ctx ctx.canonicalFreshKey .bit _)
  · exact fresh_after ((CWriteRef.retainedHead ctx ctx.canonicalFreshKey .bit _).underRetained
      (acceptedContext ctx).canonicalFreshKey (.unsignedWord width) _)
  · exact fresh_after (CWriteRef.retainedHead (acceptedContext ctx)
      (acceptedContext ctx).canonicalFreshKey (.unsignedWord width) _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Slots
