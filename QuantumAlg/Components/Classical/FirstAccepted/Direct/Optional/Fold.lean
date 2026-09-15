/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual chronological first-success folding of optional words

Every candidate is unpacked by the existing nominal instruction and passed to
actual direct selection. Source reads avoid the three real destinations, so
each step consumes its original caller value. The mathematical fold only
states the result of that complete store and instruction-history execution.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Fold

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- A structural read lies outside all three actual optional-selection destinations. -/
structure Avoids (refs : Optional.Refs ctx width) {shape : CShape}
    (input : CInputRef ctx shape) : Prop where
  accepted : refs.selection.accepted.key ∉ input.storageKeys
  selected : refs.selection.selected.key ∉ input.storageKeys
  unpacked : refs.unpacked.key ∉ input.storageKeys

/-- Every candidate remains in its original source cell throughout the real loop. -/
def InputsSeparated (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) : Prop := ∀ index, Avoids refs (inputs index)

/-- Increasing finite indices determine the actual optional-unpack and selection sequence. -/
def into (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) : Circuit ctx ctx :=
  Circuit.forRange count (fun index => Optional.into (inputs index) refs)

/-- Record the actual store and branch histories after each chronological candidate. -/
def step (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (store : Store ctx) : Store ctx × (into inputs refs).Path :=
  Circuit.forRangeRecord count (fun index => Optional.into (inputs index) refs)
    (fun index => Optional.step (inputs index) refs) store

/-- The complete actual loop changes only its classical record, retaining arbitrary
reference blocks. -/
theorem into_execute (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into inputs refs).execute Reference state = state.mapClassical (fun entry =>
      ((step inputs refs entry.1).1, (entry.2, (step inputs refs entry.1).2))) :=
  Circuit.execute_forRangeRecord count (fun index => Optional.into (inputs index) refs)
    (fun index => Optional.step (inputs index) refs)
    (fun index => Optional.into_execute (inputs index) refs) Reference state

/-- Every caller read outside the three destinations survives the complete actual loop. -/
theorem into_callerFrame (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (avoids : Avoids refs other) :
    (step inputs refs store).1.read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count induction =>
      change (step (fun index : Fin count => inputs index.succ) refs
        (Optional.step (inputs 0) refs store).1).1.read other = _
      exact (induction _ _).trans
        (Optional.into_callerFrame (inputs 0) refs store other
          avoids.accepted avoids.selected avoids.unpacked)

/-- Selection is exactly the first-success fold of the original chronological source values. -/
theorem into_correct (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (separated : Optional.Separation refs)
    (sources : InputsSeparated inputs refs) (store : Store ctx) :
    Optional.selectedValue refs.selection (step inputs refs store).1 =
      (List.ofFn (fun index => store.read (inputs index))).foldl Optional.retainValue
        (Optional.selectedValue refs.selection store) := by
  induction count generalizing store with
  | zero => rfl
  | succ count induction =>
      change Optional.selectedValue refs.selection
        (step (fun index : Fin count => inputs index.succ) refs
          (Optional.step (inputs 0) refs store).1).1 = _
      rw [induction _ (fun index => sources index.succ)]
      have reads : (fun index : Fin count =>
          (Optional.step (inputs 0) refs store).1.read (inputs index.succ)) =
          (fun index => store.read (inputs index.succ)) := by
        funext index
        exact Optional.into_callerFrame (inputs 0) refs store (inputs index.succ)
          (sources index.succ).accepted (sources index.succ).selected
          (sources index.succ).unpacked
      rw [reads, Optional.into_correct (inputs 0) refs separated store]
      rw [List.ofFn_succ, List.foldl_cons]

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Fold
