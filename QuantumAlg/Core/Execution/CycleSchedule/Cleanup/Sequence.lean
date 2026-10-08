/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Observe.Grouping
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Cleanup after an actual preceding section

The suffix's physical reset still measures and seeds the whole owned output
when an earlier section is executed first. The earlier section must separately
restore the borrowed interface; cleanup of a suffix cannot repair a preceding
violation of that interface.
-/

namespace QuantumAlg.Circuit.RestartCleanup

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre middle post : RuntimeCtx model.kind}

/-- A caller-specified physical label remains pure after finite grouping of
complete records. This refers to the unchanged circuit and original mass. -/
def GroupedPureAt (code : Circuit model pre post)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ) : Prop :=
    ∀ (Reference : Register) {H : Type} [Fintype H]
        (state : State pre Reference (model.HiddenState × H))
        {D : Type} [Fintype D]
        (read : (Store post × (model.HiddenState × (H × code.Path))) → D)
        (result : D),
        (StatePromise.pure (NormalizedVector.ket seed)).Holds
          (DensityOperator.observeSelection post.quantumLayout
            post.borrowedSelectionᶜ Reference
            (((code.execute Reference state).mapClassical read).block result))

/-- Existence of one such fixed label for all complete output groupings. -/
def GroupedPure (code : Circuit model pre post) : Prop :=
  ∃ seed, GroupedPureAt code seed

/-- The same prescribed seed survives any classical observation of full
records, with no branch renormalization or independence assumption. -/
theorem groupedPureAt {code : Circuit model pre post}
    {seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ}
    (fixed : ReinitializedAt code seed) : GroupedPureAt code seed := by
  unfold GroupedPureAt
  intro Reference H _ state D _ read result
  exact ExecutionState.observeSelected_mapClassical_pure post.quantumLayout
    post.borrowedSelectionᶜ Reference (code.execute Reference state) read
    (NormalizedVector.ket seed) (fixed Reference state) result

/-- Physical cleanup remains a mass-weighted pure output after a caller reads
any finite part of the actual store, hidden state, history and path record. -/
theorem groupedPure {code : Circuit model pre post}
    (cleanup : RestartCleanup code) : GroupedPure code := by
  unfold GroupedPure
  obtain ⟨seed, fixed⟩ := cleanup.reinitialized
  exact ⟨seed, groupedPureAt fixed⟩

/-- A preceding section cannot change the fixed owned output label prepared
by the actual physical reset at the end of the complete section. -/
theorem afterAt (first : Circuit model pre middle)
    (cleanup : Circuit model middle post)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : ReinitializedAt cleanup seed) :
    ReinitializedAt (first.seq cleanup) seed := by
  unfold ReinitializedAt at fixed ⊢
  intro Reference H _ state label
  let stage := cleanup.execute Reference (first.execute Reference state)
  let labels :
      (Store post × (model.HiddenState × ((H × first.Path) × cleanup.Path))) ≃
        (Store post × (model.HiddenState × (H × (first.Path × cleanup.Path)))) :=
    (Equiv.refl (Store post)).prodCongr
      ((Equiv.refl model.HiddenState).prodCongr
        (Equiv.prodAssoc H first.Path cleanup.Path))
  let original : Store post × (model.HiddenState × ((H × first.Path) × cleanup.Path)) :=
    (label.1, (label.2.1, ((label.2.2.1, label.2.2.2.1), label.2.2.2.2)))
  have codeEq : (first.seq cleanup).execute Reference state =
      stage.mapClassical labels := by
    simpa only [Circuit.execute_seq, State.mapHistory, stage] using
      (ExecutionState.executionState_mapClassical_congr_decision stage
        (fun entry => (entry.1,
          (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
        labels (by intro entry; rfl) _ _)
  have blockEq : ((first.seq cleanup).execute Reference state).block label =
      stage.block original := by
    calc
      _ = (stage.mapClassical labels).block label :=
        congrArg (fun output => output.block label) codeEq
      _ = stage.block (labels.symm label) :=
        ExecutionState.coordinate_mapClassical_block stage labels label
      _ = stage.block original := by rfl
  rw [blockEq]
  exact fixed Reference (first.execute Reference state) original

/-- Compose a borrowed-restoring first with an actual complete reset at the
end, retaining the same fixed seed on every complete output record. -/
theorem after (first : Circuit model pre middle) (cleanup : Circuit model middle post)
    (firstRestores : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : State pre Reference (model.HiddenState × H)),
      first.BorrowedRestored Reference state (first.execute Reference state))
    (reset : RestartCleanup cleanup) : RestartCleanup (first.seq cleanup) := by
  obtain ⟨seed, reinitialized⟩ := reset.reinitialized
  refine ⟨?_, ?_, ⟨seed, ?_⟩⟩
  · intro path
    obtain ⟨dimension, present⟩ := reset.measured path.2
    exact ⟨dimension, by
      change Resource.Event.measurement dimension ∈
        first.eventTrace path.1 ++ cleanup.eventTrace path.2
      exact List.mem_append.mpr (Or.inr present)⟩
  · intro Reference H _ state
    exact Circuit.borrowedRestored_seq first cleanup state
      (firstRestores Reference state) (reset.restores Reference _)
  · exact afterAt first cleanup seed reinitialized

end

end QuantumAlg.Circuit.RestartCleanup
