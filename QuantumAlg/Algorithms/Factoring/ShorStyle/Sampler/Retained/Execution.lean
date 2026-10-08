/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Semantics
import all QuantumAlg.Core.Execution.Random.Map

/-!
# Complete execution equation for retained residue sampling

The actual allocation and sampled body compose into one independent uniform
source followed by the mathematically specified complete result store. Each
original quantum-reference block is retained with its exact uniform weight.
The recorded path is the actual circuit path, not additional live storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]

private theorem mapClassical_congr_decision {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (state : ExecutionState C R) (left right : C → D)
    (same : ∀ entry, left entry = right entry) (firstDecision secondDecision : DecidableEq D) :
    @ExecutionState.mapClassical C D _ _ R firstDecision state left =
      @ExecutionState.mapClassical C D _ _ R secondDecision state right := by
  have decisionEquality : firstDecision = secondDecision := Subsingleton.elim _ _
  subst secondDecision
  exact congrArg (fun update =>
    @ExecutionState.mapClassical C D _ _ R firstDecision state update) (funext same)

private theorem uniform_map_composition {C A B D : Type}
    [Fintype C] [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) (allocate : C → A)
    (advance : A × Fin count → B) (regroup : B → D) :
    ((uniformChoice (state.mapClassical allocate) count).mapClassical advance).mapClassical
        regroup =
      (uniformChoice state count).mapClassical
        ((regroup ∘ advance) ∘ (fun entry => (allocate entry.1, entry.2))) := by
  have sampled := congrArg
    (fun source : ExecutionState (A × Fin count) R => source.mapClassical (regroup ∘ advance))
    (uniformChoice_mapClassical state count allocate)
  exact (ExecutionState.executionState_mapClassical_comp
    (uniformChoice (state.mapClassical allocate) count) advance regroup).trans
    (sampled.trans (ExecutionState.executionState_mapClassical_comp
      (uniformChoice state count) (fun entry => (allocate entry.1, entry.2))
      (regroup ∘ advance)))

/-- Actual allocation and sampled instruction path for one source integer. -/
def resultPath (ctx : RuntimeCtx model.kind) (N : Nat) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) : (circuit (model := model) ctx N).Path :=
  (((), ()), (outcomeStep (model := model) ctx N (pushStore N store) value).2)

private theorem sampled_update_of_eq {C A B D : Type}
    [Fintype C] [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (allocated : ExecutionState A R)
    (computed : ExecutionState B R) (count : ℕ+)
    (allocate : C → A) (advance : A × Fin count → B) (regroup : B → D)
    (allocationEquation : allocated = state.mapClassical allocate)
    (bodyEquation : computed = (uniformChoice allocated count).mapClassical advance) :
    computed.mapClassical regroup = (uniformChoice state count).mapClassical
      ((regroup ∘ advance) ∘ (fun entry => (allocate entry.1, entry.2))) := by
  have bodyMap := congrArg (fun final : ExecutionState B R => final.mapClassical regroup)
    bodyEquation
  have allocationMap := congrArg (fun initial : ExecutionState A R =>
    ((uniformChoice initial count).mapClassical advance).mapClassical regroup) allocationEquation
  exact bodyMap.trans (allocationMap.trans
    (uniform_map_composition state count allocate advance regroup))

omit [BitWord.Selected model] in
private theorem execute_seq_mapped {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute Reference state =
      (second.execute Reference (first.execute Reference state)).mapClassical
        (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))) := by
  refine (Circuit.execute_seq first second state).trans ?_
  unfold State.mapHistory
  exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

private def allocateRecord (ctx : RuntimeCtx model.kind) (N : Nat) {History : Type} :
    Store ctx × (model.HiddenState × History) →
      Store (context ctx N) × (model.HiddenState × (History × (allocation (model := model)
          ctx N).Path)) :=
  fun entry => (pushStore N entry.1, (entry.2.1, (entry.2.2, ((), ()))))

omit [BitWord.Selected model] in
private theorem allocation_record_execute (ctx : RuntimeCtx model.kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (allocation (model := model)
        ctx N).execute Reference state =
      state.mapClassical (allocateRecord (model := model) ctx N) := by
  refine (samplerRetained_allocation_execute ctx N Reference state).trans ?_
  exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

private def bodyRecord (ctx : RuntimeCtx model.kind) {N : Nat} (input : Input N) {History : Type} :
    (Store (context ctx N) × (model.HiddenState × History)) × Fin (2 ^ residueSamplingBits N) →
      Store (context ctx N) × (model.HiddenState × (History × (body (model := model)
          ctx N).Path)) := fun entry =>
  (outputStore input entry.1.1 entry.2, (entry.1.2.1, (entry.1.2.2, (outcomeStep (model := model)
      ctx N entry.1.1 entry.2).2)))

private theorem body_record_execute (ctx : RuntimeCtx model.kind) {N : Nat} (input : Input N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) ctx N).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (bodyRecord (model := model) ctx input) := by
  refine (samplerRetained_body_source_execute ctx input Reference state).trans ?_
  exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

/-- Full native sampling implements the source law on the complete mathematical result store. -/
theorem samplerRetained_execute (ctx : RuntimeCtx model.kind) {N : Nat} (input : Input N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (circuit (model := model) ctx N).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => (resultStore input entry.1.1 entry.2,
          (entry.1.2.1, (entry.1.2.2, resultPath (model := model) ctx N entry.1.1 entry.2)))) := by
  have composed := sampled_update_of_eq state
    ((allocation (model := model) ctx N).execute Reference state)
    ((body (model := model)
        ctx N).execute Reference ((allocation (model := model) ctx N).execute Reference state))
    ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
    (allocateRecord (model := model) ctx N) (bodyRecord (model := model) ctx input)
    (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
    (allocation_record_execute (model := model) ctx N Reference state)
    (by
      refine (body_record_execute (model := model) ctx input Reference
        ((allocation (model := model) ctx N).execute Reference state)).trans ?_
      exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _)
  refine (execute_seq_mapped (allocation (model := model)
      ctx N) (body (model := model) ctx N) Reference state).trans
    (composed.trans ?_)
  exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
