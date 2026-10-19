/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual signed-word normalization

Sign classification feeds its real stored bit into the magnitude branch.
The incoming magnitude word and flag may contain arbitrary values. The two
or three actual instructions overwrite those cells, preserve all other reads,
and retain every live system and borrowed correlation.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual sign write followed by the branch that reads that same cell. -/
def normalizeMagnitude (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (classifySign (model := model) raw negative) (selectMagnitude (model := model) raw
    (writeInput negative) work)

/-- The chronological store updates and path of the real normalization circuit. -/
def normalizationStep (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx × (normalizeMagnitude (model := model) raw negative work).Path
      :=
  let signed := signStore raw negative store
  let magnitude := magnitudeStep (model := model) raw (writeInput negative) work signed
  (magnitude.1, (signPath (model := model) raw negative store, magnitude.2))

/-- The full normalization interpreter follows its actual sign result on every input block. -/
lemma normalizeMagnitude_execute (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (normalizeMagnitude (model := model) raw negative work).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := normalizationStep (model := model) raw negative work entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [normalizeMagnitude, normalizationStep, Circuit.execute_seq, classifySign_execute,
    selectMagnitude_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual sign-producing prefix discharges the selected arm's sign requirement. -/
lemma normalizeMagnitude_correct (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (rawAvoidsFlag : negative.key ∉ raw.storageKeys) :
    (((normalizationStep (model := model) raw negative work store).1).read (writeInput
      work)).toNat =
      rawMagnitude (store.read raw) := by
  have rawFrame := classifySign_callerFrame raw negative store raw rawAvoidsFlag
  have selected := rawWord_selectMagnitude_correct raw (writeInput negative) work
    (signStore raw negative store) (by rw [rawWord_classifySign_correct, rawFrame])
  simpa only [normalizationStep, rawFrame] using selected

/-- The magnitude update keeps the already written sign for the following division stages. -/
lemma normalizeMagnitude_sign (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (separate : work.key ≠ negative.key) :
    (((normalizationStep (model := model) raw negative work store).1).read (writeInput
      negative)).toBool =
      rawIsNegative (store.read raw) := by
  have frame := selectMagnitude_callerFrame raw (writeInput negative) work
    (signStore raw negative store) (writeInput negative)
    (by simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using separate)
  change (((magnitudeStep (model := model) raw (writeInput negative) work
    (signStore raw negative store)).1).read (writeInput negative)).toBool = _
  rw [frame, rawWord_classifySign_correct]

/-- Normalization preserves every read outside its two actual output cells. -/
lemma normalizeMagnitude_callerFrame (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoidsFlag : negative.key ∉ other.storageKeys)
    (avoidsMagnitude : work.key ∉ other.storageKeys) :
    ((normalizationStep (model := model) raw negative work store).1).read other = store.read other
      :=
  (selectMagnitude_callerFrame raw (writeInput negative) work
    (signStore raw negative store) other avoidsMagnitude).trans
      (classifySign_callerFrame raw negative store other avoidsFlag)

/-- Every chosen magnitude arm restores the complete borrowed interface. -/
lemma selectMagnitude_borrowedRestored (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectMagnitude (model := model) raw negative work).BorrowedRestored Reference state
      ((selectMagnitude (model := model) raw negative work).execute environment
        Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment)
  intro value _history _ current
  cases value with
  | bit flag =>
      cases flag
      · exact Circuit.borrowedRestored_classical (environment := environment) _ current
      · exact Circuit.borrowedRestored_seq (environment := environment) _ _ current
          (Circuit.borrowedRestored_classical (environment := environment) _ current)
          (Circuit.borrowedRestored_classical (environment := environment) _ _)

/-- Sign classification and selected magnitude jointly restore every borrowed correlation. -/
lemma normalizeMagnitude_borrowedRestored (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (normalizeMagnitude (model := model) raw negative work).BorrowedRestored Reference state
      ((normalizeMagnitude (model := model) raw negative work).execute environment
        Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (classifySign_borrowedRestored raw negative Reference state)
    (selectMagnitude_borrowedRestored raw (writeInput negative) work Reference _)

/-- Actual normalization records the sign instruction and only its selected magnitude arm. -/
lemma normalizeMagnitude_events (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (normalizeMagnitude (model := model) raw negative work).Path) :
    (normalizeMagnitude (model := model) raw negative work).eventTrace path =
      signTrace (model := model) width ++ magnitudeTrace (model := model) width path.2.1.toBool :=
        by
  change (classifySign (model := model) raw negative).eventTrace path.1 ++
    (selectMagnitude (model := model) raw (writeInput negative) work).eventTrace path.2 = _
  rw [classifySign_events, selectMagnitude_events]

/-- The path produced from an actual store records that store's computed sign. -/
lemma normalizeMagnitude_actualEvents (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (normalizeMagnitude (model := model) raw negative work).eventTrace
      (normalizationStep (model := model) raw negative work store).2 =
        signTrace (model := model) width ++ magnitudeTrace (model := model) width (rawIsNegative
          (store.read raw)) := by
  rw [normalizeMagnitude_events]
  change signTrace (model := model) width ++ magnitudeTrace (model := model) width
    ((signStore raw negative store).read (writeInput negative)).toBool = _
  rw [rawWord_classifySign_correct]

/-- Unit native durations retain the dependence from sign write to selected arithmetic. -/
lemma normalizeMagnitude_depth_le (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (normalizeMagnitude (model := model) raw negative work).Path) :
    (normalizeMagnitude (model := model) raw negative work).depth (fun _ => 1) path ≤ 3 := by
  rcases path with ⟨signRecord, flag, armRecord⟩
  cases flag with
  | bit flag =>
      cases width <;> cases flag
      all_goals first | exact (by decide : 2 ≤ 3) | exact (by decide : 3 ≤ 3)

/-- The complete real normalization uses at most three native classical instructions. -/
lemma normalizeMagnitude_eventCount_le (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (normalizeMagnitude (model := model) raw negative work).Path) :
    ((normalizeMagnitude (model := model) raw negative work).eventTrace path).length ≤ 3 := by
  rw [normalizeMagnitude_events]
  simp only [List.length_append, signTrace, List.length_cons, List.length_nil]
  unfold magnitudeTrace
  split <;> simp only [List.length_cons, List.length_nil] <;> decide

/-- The real control flow visits only the original live context. -/
lemma normalizeMagnitude_visited (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (normalizeMagnitude (model := model) raw negative work).Path) :
    (normalizeMagnitude (model := model) raw negative work).visitedContexts path =
      if path.2.1.toBool then [ctx, ctx, ctx] else [ctx, ctx] := by
  rcases path with ⟨signRecord, flag, armRecord⟩
  cases flag with
  | bit flag => cases width <;> cases flag <;> rfl

/-- Resident space includes both output cells and every pre-existing quantum dimension. -/
lemma normalizeMagnitude_resident_le (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (normalizeMagnitude (model := model) raw negative work).Path) :
    (normalizeMagnitude (model := model) raw negative work).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [normalizeMagnitude_visited] at present
  split at present <;> simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  all_goals subst visited; exact le_rfl

/-- Auxiliary space uses exactly the already supplied roles, with no extra temporary cell. -/
lemma normalizeMagnitude_auxiliary_le (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (normalizeMagnitude (model := model) raw negative work).Path) :
    (normalizeMagnitude (model := model) raw negative work).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [normalizeMagnitude_visited] at present
  split at present <;> simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  all_goals subst visited; exact le_rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord
