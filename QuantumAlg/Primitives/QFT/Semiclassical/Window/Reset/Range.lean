/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual finite records on an internally preserved invariant

The width and component circuits remain symbolic. The predicate may describe
zero support of a reset bank; it is used only to invoke the proved actual
component equation. Every intermediate caller Store, hidden service state
and complete chronological Path is retained.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma sequence_records_at {model : ExecutionModel} {base : RuntimeCtx model.kind}
    {allowAllocation : Bool} (first second : Circuit model base base allowAllocation)
    (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (head : Store base → Store base × first.Path)
    (tail : Store base → Store base × second.Path)
    (firstEquation : first.execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := head entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (secondEquation : second.execute environment Reference
        (first.execute environment Reference state) =
      (first.execute environment Reference state).mapClassical (fun entry =>
        let result := tail entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2))))) :
    (first.seq second).execute environment Reference state =
      state.mapClassical (fun entry =>
        let left := head entry.1
        let right := tail left.1
        (right.1, (entry.2.1, (entry.2.2, (left.2, right.2))))) := by
  rw [Circuit.execute_seq, secondEquation, firstEquation]
  dsimp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual finite execution retains its complete deterministic records on an invariant. -/
lemma window_reset_range_records_on_invariant {model : ExecutionModel}
    {base : RuntimeCtx model.kind}
    {allowAllocation : Bool} (count : Nat)
    (body : Fin count → Circuit model base base allowAllocation)
    (environment : model.Environment) (Reference : Register)
    (records : ∀ index, Store base → Store base × (body index).Path)
    (goodState : {History : Type} → [Fintype History] →
      State base Reference (model.HiddenState × History) → Prop)
    (steps : ∀ index {History : Type} [Fintype History]
      (state : State base Reference (model.HiddenState × History)), goodState state →
      (body index).execute environment Reference state = state.mapClassical (fun entry =>
        let result := records index entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (preserves : ∀ index {History : Type} [Fintype History]
      (state : State base Reference (model.HiddenState × History)), goodState state →
      goodState ((body index).execute environment Reference state))
    {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History)) (good : goodState state) :
    (Circuit.forRange count body).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := Circuit.forRangeStoreRecord count body records entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction count generalizing History with
  | zero =>
      exact (Circuit.execute_id_mapClassical (allowAllocation := allowAllocation)
        (model := model) (environment := environment) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ count ih =>
      have composed := sequence_records_at (body 0)
        (Circuit.forRange count (fun index => body index.succ)) environment Reference state
        (records 0)
        (Circuit.forRangeStoreRecord count (fun index => body index.succ)
          (fun index => records index.succ))
        (steps 0 state good)
        ((ih (fun index => body index.succ) (fun index => records index.succ)
          (fun index => steps index.succ) (fun index => preserves index.succ)
          ((body 0).execute environment Reference state) (preserves 0 state good)).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl))
      exact composed.trans (ExecutionState.executionState_mapClassical_congr state rfl)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
