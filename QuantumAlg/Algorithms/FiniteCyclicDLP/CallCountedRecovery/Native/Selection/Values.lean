/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection.Correctness

/-!
# Mathematical witnesses for the actual first-success result

The complete-store theorem already identifies the actual result with the
original checked-candidate fold. These pure consequences identify its chosen
member and transfer a common accepted value to that result. They impose no
additional runtime input or stopping rule.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

private theorem retain_some {α : Type} (values : List (Option α)) (value : α) :
    values.foldl FirstAccepted.retainFirst (some value) = some value := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact ih

private theorem retained_mem {α : Type} (values : List (Option α)) (value : α)
    (selected : values.foldl FirstAccepted.retainFirst none = some value) :
    some value ∈ values := by
  induction values with
  | nil => cases selected
  | cons head tail ih =>
      cases head with
      | none => exact List.mem_cons_of_mem _ (ih selected)
      | some word =>
          have same : word = value := Option.some.inj ((retain_some tail word).symm.trans selected)
          subst word
          exact List.mem_cons_self

private theorem retained_unique {α : Type} (values : List (Option α)) (value : α)
    (unique : ∀ word, some word ∈ values → word = value)
    (present : some value ∈ values) :
    values.foldl FirstAccepted.retainFirst none = some value := by
  induction values with
  | nil => cases present
  | cons head tail ih =>
      cases head with
      | none =>
          apply ih
          · exact fun word member => unique word (List.mem_cons_of_mem _ member)
          · exact (List.mem_cons.mp present).resolve_left (by intro impossible; cases impossible)
      | some word =>
          rw [unique word List.mem_cons_self]
          exact retain_some tail value

private theorem recovery_fold (P : Parameters G) (count : Nat)
    (inputs : Fin count → CShape.Value (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CShape.Word P.width) :
    groupRecoveryValue P count inputs target =
      match (List.ofFn fun index =>
        if attemptAcceptedValue P (inputs index) target then
          some (attemptCandidateValue P (inputs index)) else none).foldl
            FirstAccepted.retainFirst none with
      | none => CShape.Value.optionNone
      | some value => CShape.Value.optionSome value := by
  unfold groupRecoveryValue
  have values : (List.ofFn fun index => attemptOption P (inputs index) target) =
      List.ofFn (fun index => if attemptAcceptedValue P (inputs index) target then
        some (attemptCandidateValue P (inputs index)) else none) := by
    congr 1
  rw [values]
  cases (List.ofFn fun index => if attemptAcceptedValue P (inputs index) target then
    some (attemptCandidateValue P (inputs index)) else none).foldl
      FirstAccepted.retainFirst none <;> rfl

/-- Every returned word belongs to an actual accepted candidate of the original sample order. -/
theorem groupRecoveryValue_some_mem (P : Parameters G) (count : Nat)
    (inputs : Fin count → CShape.Value (.fixedVector (P.width + P.width) (.finite 2)))
    (target word : CShape.Word P.width)
    (selected : groupRecoveryValue P count inputs target = .optionSome word) :
    ∃ index, attemptAcceptedValue P (inputs index) target = true ∧
      attemptCandidateValue P (inputs index) = word := by
  let candidates := List.ofFn fun index =>
    if attemptAcceptedValue P (inputs index) target then
      some (attemptCandidateValue P (inputs index)) else none
  have returned : candidates.foldl FirstAccepted.retainFirst none = some word := by
    rw [recovery_fold] at selected
    change (match candidates.foldl FirstAccepted.retainFirst none with
      | none => CShape.Value.optionNone
      | some value => CShape.Value.optionSome value) = .optionSome word at selected
    cases choice : candidates.foldl FirstAccepted.retainFirst none with
    | none => rw [choice] at selected; cases selected
    | some value =>
        rw [choice] at selected
        exact congrArg some (CShape.Value.optionSome.inj selected)
  obtain ⟨index, member⟩ := List.mem_ofFn.mp (retained_mem candidates word returned)
  by_cases accepted : attemptAcceptedValue P (inputs index) target = true
  · refine ⟨index, accepted, ?_⟩
    exact Option.some.inj (by simpa only [accepted, if_true] using member)
  · simp only [accepted] at member
    cases member

/-- A selected sample and uniqueness of accepted words determine the complete first-success value.

The endpoint derives these mathematical premises from its original group
encoding and selected-outcome event; they are not extra inputs to the circuit.
-/
theorem groupRecoveryValue_eq_some_of_accepted (P : Parameters G) (count : Nat)
    (inputs : Fin count → CShape.Value (.fixedVector (P.width + P.width) (.finite 2)))
    (target word : CShape.Word P.width)
    (present : ∃ index, attemptAcceptedValue P (inputs index) target = true)
    (unique : ∀ index, attemptAcceptedValue P (inputs index) target = true →
      attemptCandidateValue P (inputs index) = word) :
    groupRecoveryValue P count inputs target = .optionSome word := by
  let candidates := List.ofFn fun index =>
    if attemptAcceptedValue P (inputs index) target then
      some (attemptCandidateValue P (inputs index)) else none
  have members : ∀ value, some value ∈ candidates → value = word := by
    intro value member
    obtain ⟨index, actual⟩ := List.mem_ofFn.mp member
    by_cases accepted : attemptAcceptedValue P (inputs index) target = true
    · have same : attemptCandidateValue P (inputs index) = value :=
        Option.some.inj (by simpa only [accepted, if_true] using actual)
      exact same.symm.trans (unique index accepted)
    · simp only [accepted] at actual
      cases actual
  have chosen : some word ∈ candidates := by
    obtain ⟨index, accepted⟩ := present
    apply List.mem_ofFn.mpr
    exact ⟨index, by simp only [accepted, if_true, unique index accepted]⟩
  have result := retained_unique candidates word members chosen
  rw [recovery_fold]
  change (match candidates.foldl FirstAccepted.retainFirst none with
    | none => CShape.Value.optionNone
    | some value => CShape.Value.optionSome value) = .optionSome word
  rw [result]

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
