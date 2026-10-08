/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Deterministic
import all QuantumAlg.Core.Execution.Retained.Record
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Actual final retained records preserve a completed physical seed
-/

namespace QuantumAlg.Circuit.RestartCleanup

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical

variable {model : ExecutionModel} {pre ctx : RuntimeCtx model.kind}
  {key : StorageKey} {shape : CShape} {fresh : key ∉ ctx.keys}

/-- Real result retention and its deterministic native body preserve the completed physical seed. -/
theorem followedByRetainedAt (first : Circuit model pre ctx)
    (second : Circuit model ctx (ctx.addRetained key shape fresh))
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : ReinitializedAt first seed)
    (step : Store ctx × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × second.Path)
    (equation : RetainedRecord second step) :
    ReinitializedAt (first.seq second) seed := by
  unfold ReinitializedAt at fixed ⊢
  intro Reference History _ state record
  rw [Circuit.execute_seq]
  unfold State.mapHistory
  apply selectedPureMapDecision (ctx.addRetained key shape fresh).quantumLayout
    (ctx.addRetained key shape fresh).borrowedSelectionᶜ Reference _
    (second.execute Reference (first.execute Reference state))
    (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
    (NormalizedVector.ket seed) _ record
  intro intermediate
  rw [equation]
  exact selectedPureMapDecision ctx.quantumLayout ctx.borrowedSelectionᶜ Reference _
    (first.execute Reference state)
    (fun entry => let result := step (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2))))
    (NormalizedVector.ket seed) (fixed Reference state) intermediate

/-- The same actual measurement and borrowed restoration survive the paid final result pack. -/
theorem followedByRetained (first : Circuit model pre ctx)
    (second : Circuit model ctx (ctx.addRetained key shape fresh))
    (cleanup : RestartCleanup first)
    (step : Store ctx × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × second.Path)
    (equation : RetainedRecord second step)
    (restores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.BorrowedRestored Reference state (second.execute Reference state)) :
    RestartCleanup (first.seq second) := by
  obtain ⟨seed, fixed⟩ := cleanup.reinitialized
  refine ⟨?_, ?_, ⟨seed, followedByRetainedAt first second seed fixed step equation⟩⟩
  · intro path
    obtain ⟨dimension, present⟩ := cleanup.measured path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  · intro Reference History _ state
    exact Circuit.borrowedRestored_seq first second state
      (cleanup.restores Reference state) (restores Reference _)

end

end QuantumAlg.Circuit.RestartCleanup
