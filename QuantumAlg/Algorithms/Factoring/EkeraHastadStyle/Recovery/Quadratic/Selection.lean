/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!+# Actual left-priority selection of the two checked quadratic candidates

Two executions of the existing first-accepted circuit consume the two stored
validity bits in source order. The same persistent latches remember both an
earlier pair and the first candidate of this pair. This component does not
recompute validity, initialize latches or skip either preceding factor check.
Its complete store equation preserves arbitrary quantum-reference correlations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Selection

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Consume the two already checked candidates using the same actual persistent latches. -/
def code (first second : FirstAccepted.Inputs ctx width) (refs : FirstAccepted.Refs ctx width) :
    Circuit ctx ctx :=
  .seq (FirstAccepted.circuit first refs) (FirstAccepted.circuit second refs)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The two actual selector executions and their chronological branch paths. -/
def step (first second : FirstAccepted.Inputs ctx width) (refs : FirstAccepted.Refs ctx width)
    (store : Store ctx) : Store ctx × (code first second refs).Path :=
  let initial := FirstAccepted.step first refs store
  let final := FirstAccepted.step second refs initial.1
  (final.1, (initial.2, final.2))

/-- The exact two-step execution retains the original full quantum-reference blocks. -/
theorem nativeQuadratic_selection_execute (first second : FirstAccepted.Inputs ctx width)
    (refs : FirstAccepted.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code first second refs).execute Reference state = state.mapClassical (fun entry =>
      ((step first second refs entry.1).1, (entry.2, (step first second refs entry.1).2))) := by
  simp only [code, Circuit.execute_seq, FirstAccepted.firstAccepted_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (code first second refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry =>
          ((step first second refs entry.1).1, (entry.2, (step first second refs entry.1).2))))
    (Subsingleton.elim _ _)

end

/-- Internal cell separation, later discharged by the actual enclosing workspace positions. -/
structure Separated (first second : FirstAccepted.Inputs ctx width)
    (refs : FirstAccepted.Refs ctx width) : Prop where
  /-- The first real selector receives valid nonaliasing positions. -/
  firstSeparated : FirstAccepted.Separated first refs
  /-- The second real selector receives valid nonaliasing positions. -/
  secondSeparated : FirstAccepted.Separated second refs
  /-- The first selector preserves the second candidate's stored validity bit. -/
  availableEligible : refs.available.key ∉ second.eligible.storageKeys
  takeEligible : refs.take.key ∉ second.eligible.storageKeys
  acceptedEligible : refs.accepted.key ∉ second.eligible.storageKeys
  selectedEligible : refs.selected.key ∉ second.eligible.storageKeys
  /-- The first selector preserves the second candidate word before its possible copy. -/
  availableCandidate : refs.available.key ∉ second.candidate.storageKeys
  takeCandidate : refs.take.key ∉ second.candidate.storageKeys
  acceptedCandidate : refs.accepted.key ∉ second.candidate.storageKeys
  selectedCandidate : refs.selected.key ∉ second.candidate.storageKeys

private theorem choice_order {α : Type} (accepted firstValid secondValid : Bool)
    (old first second : α) :
    (if (!(accepted || firstValid)) && secondValid then second
      else if (!accepted) && firstValid then first else old) =
      (if accepted then old else
        if firstValid then first else if secondValid then second else old) :=
  by cases accepted <;> cases firstValid <;> cases secondValid <;> rfl

/-- Actual latches preserve earlier acceptance and otherwise implement the source's left priority.
-/
theorem nativeQuadratic_selection_latches (first second : FirstAccepted.Inputs ctx width)
    (refs : FirstAccepted.Refs ctx width) (separated : Separated first second refs)
    (store : Store ctx) :
    let final := (step first second refs store).1
    (final.read (FirstAccepted.cellRead refs.accepted)).toBool =
        (((store.read (FirstAccepted.cellRead refs.accepted)).toBool ||
          (store.read first.eligible).toBool) || (store.read second.eligible).toBool) ∧
      final.read (FirstAccepted.cellRead refs.selected) =
        if (store.read (FirstAccepted.cellRead refs.accepted)).toBool then
          store.read (FirstAccepted.cellRead refs.selected)
        else if (store.read first.eligible).toBool then store.read first.candidate
        else if (store.read second.eligible).toBool then store.read second.candidate
        else store.read (FirstAccepted.cellRead refs.selected) := by
  let initial := (FirstAccepted.step first refs store).1
  have firstLaw := FirstAccepted.firstAccepted_latches first refs separated.firstSeparated store
  have secondLaw :=
    FirstAccepted.firstAccepted_latches second refs separated.secondSeparated initial
  have secondEligible := FirstAccepted.firstAccepted_read_other first refs second.eligible
    separated.availableEligible separated.takeEligible separated.acceptedEligible
    separated.selectedEligible store
  have secondCandidate := FirstAccepted.firstAccepted_read_other first refs second.candidate
    separated.availableCandidate separated.takeCandidate separated.acceptedCandidate
    separated.selectedCandidate store
  refine ⟨secondLaw.1.trans ?_, secondLaw.2.trans ?_⟩
  · rw [firstLaw.1, secondEligible]
  · rw [firstLaw.1, secondEligible, firstLaw.2, secondCandidate]
    exact choice_order _ _ _ _ _ _

/-- All other stored reads retain their complete values through both actual selector paths. -/
theorem nativeQuadratic_selection_read_other (first second : FirstAccepted.Inputs ctx width)
    (refs : FirstAccepted.Refs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (availableFree : refs.available.key ∉ other.storageKeys)
    (takeFree : refs.take.key ∉ other.storageKeys)
    (acceptedFree : refs.accepted.key ∉ other.storageKeys)
    (selectedFree : refs.selected.key ∉ other.storageKeys) (store : Store ctx) :
    (step first second refs store).1.read other = store.read other :=
  (FirstAccepted.firstAccepted_read_other second refs other availableFree takeFree
    acceptedFree selectedFree (FirstAccepted.step first refs store).1).trans
    (FirstAccepted.firstAccepted_read_other first refs other availableFree takeFree
      acceptedFree selectedFree store)

/-- Complete borrowed classical-quantum-reference restoration follows the two actual executions. -/
theorem nativeQuadratic_selection_borrowedRestored (first second : FirstAccepted.Inputs ctx width)
    (refs : FirstAccepted.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code first second refs).BorrowedRestored Reference state
      ((code first second refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (FirstAccepted.circuit first refs)
    (FirstAccepted.circuit second refs) state
    (FirstAccepted.firstAccepted_borrowedRestored first refs Reference state)
    (FirstAccepted.firstAccepted_borrowedRestored second refs Reference _)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Selection
