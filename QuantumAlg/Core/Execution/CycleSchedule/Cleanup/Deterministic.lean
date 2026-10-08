/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Sequence
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Observe.Grouping
import all QuantumAlg.Core.Execution.State

/-!
# Fixed physical restart through an actual deterministic store update

A proved full execution equation transports every complete density block.
The final native classical feedback may group old records but cannot change
their common fixed physical seed. Both full borrowed-restoration proofs remain
required; this transport provides no independently specified cycle protocol.
-/

namespace QuantumAlg.Circuit.RestartCleanup

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical

private theorem selectedPureMapDecision {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (Reference : Register)
    {C D : Type} [Fintype C] [Fintype D] (decision : DecidableEq D)
    (state : ExecutionState C (layout.register.prod Reference)) (read : C → D)
    (target : NormalizedVector (layout.selectedRegister selection))
    (holds : ∀ entry, (StatePromise.pure target).Holds
      (DensityOperator.observeSelection layout selection Reference (state.block entry)))
    (result : D) :
    (StatePromise.pure target).Holds
      (DensityOperator.observeSelection layout selection Reference
        ((@ExecutionState.mapClassical C D _ _ _ decision state read).block result)) := by
  rw [Subsingleton.elim decision (Classical.decEq D)]
  exact ExecutionState.observeSelected_mapClassical_pure layout selection Reference
    state read target holds result


variable {model : ExecutionModel} {pre ctx : RuntimeCtx model.kind}

/-- A real deterministic final store update preserves the predetermined seed of every block. -/
theorem followedByMapAt (first : Circuit model pre ctx) (second : Circuit model ctx ctx)
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : ReinitializedAt first seed)
    (step : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2))))) :
    ReinitializedAt (first.seq second) seed := by
  unfold ReinitializedAt at fixed ⊢
  intro Reference History _ state record
  rw [Circuit.execute_seq]
  unfold State.mapHistory
  apply selectedPureMapDecision ctx.quantumLayout
    ctx.borrowedSelectionᶜ Reference _ (second.execute Reference (first.execute Reference state))
    (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
    (NormalizedVector.ket seed) _ record
  intro intermediate
  rw [equation]
  exact selectedPureMapDecision ctx.quantumLayout
    ctx.borrowedSelectionᶜ Reference _ (first.execute Reference state)
    (fun entry => let result := step (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2))))
    (NormalizedVector.ket seed) (fixed Reference state) intermediate


/-- The full physical certificate survives paid deterministic feedback on the same live wires. -/
theorem followedByMap (first : Circuit model pre ctx) (second : Circuit model ctx ctx)
    (cleanup : RestartCleanup first)
    (step : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (restores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.BorrowedRestored Reference state (second.execute Reference state)) :
    RestartCleanup (first.seq second) := by
  obtain ⟨seed, fixed⟩ := cleanup.reinitialized
  refine ⟨?_, ?_, ⟨seed, followedByMapAt first second seed fixed step equation⟩⟩
  · intro path
    obtain ⟨dimension, present⟩ := cleanup.measured path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  · intro Reference History _ state
    exact Circuit.borrowedRestored_seq first second state
      (cleanup.restores Reference state) (restores Reference _)

end

end QuantumAlg.Circuit.RestartCleanup
