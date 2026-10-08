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

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Increasing finite indices determine the actual optional-unpack and selection sequence. -/
def into (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) : Circuit model ctx ctx :=
  Circuit.forRange count (fun index => Optional.into (model := model) (inputs index) refs)

/-- Record the actual store and service state through every chronological candidate. -/
def step (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (entry : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) × (into (model := model) inputs refs).Path :=
  Circuit.forRangeRecord count
    (fun index => Optional.into (model := model) (inputs index) refs)
    (fun index before =>
      let actual := Optional.step (model := model) (inputs index) refs before.1
      ((actual.1, before.2), actual.2)) entry

/-- Every actual iteration retains arbitrary references and the persistent service record. -/
theorem into_execute (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := step (model := model) inputs refs (entry.1, entry.2.1)
        (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))) :=
  Circuit.execute_forRangeRecord count
    (fun index => Optional.into (model := model) (inputs index) refs)
    (fun index before =>
      let actual := Optional.step (model := model) (inputs index) refs before.1
      ((actual.1, before.2), actual.2))
    (fun index reference _history _ state =>
      Optional.into_execute (inputs index) refs reference state) Reference state

/-- Every caller read outside the three destinations survives the complete actual loop. -/
theorem into_callerFrame (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (entry : Store ctx × model.HiddenState) {shape : CShape}
    (other : CInputRef ctx shape) (avoids : Avoids refs other) :
    (step (model := model) inputs refs entry).1.1.read other = entry.1.read other := by
  induction count generalizing entry with
  | zero => rfl
  | succ count induction =>
      change (step (model := model) (fun index : Fin count => inputs index.succ) refs
        ((Optional.step (model := model) (inputs 0) refs entry.1).1, entry.2)).1.1.read other = _
      exact (induction _ _).trans
        (Optional.into_callerFrame (inputs 0) refs entry.1 other
          avoids.accepted avoids.selected avoids.unpacked)

/-- Selection is exactly the first-success fold of the original chronological source values. -/
theorem into_correct (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (separated : Optional.Separation refs)
    (sources : InputsSeparated inputs refs) (entry : Store ctx × model.HiddenState) :
    Optional.selectedValue refs.selection (step (model := model) inputs refs entry).1.1 =
      (List.ofFn (fun index => entry.1.read (inputs index))).foldl Optional.retainValue
        (Optional.selectedValue refs.selection entry.1) := by
  induction count generalizing entry with
  | zero => rfl
  | succ count induction =>
      change Optional.selectedValue refs.selection
        (step (model := model) (fun index : Fin count => inputs index.succ) refs
          ((Optional.step (model := model) (inputs 0) refs entry.1).1, entry.2)).1.1 = _
      rw [induction _ (fun index => sources index.succ)]
      have reads : (fun index : Fin count =>
          (Optional.step (model := model) (inputs 0) refs entry.1).1.read (inputs index.succ)) =
          (fun index => entry.1.read (inputs index.succ)) := by
        funext index
        exact Optional.into_callerFrame (inputs 0) refs entry.1 (inputs index.succ)
          (sources index.succ).accepted (sources index.succ).selected
          (sources index.succ).unpacked
      rw [reads, Optional.into_correct (inputs 0) refs separated entry.1]
      rw [List.ofFn_succ, List.foldl_cons]

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Fold
