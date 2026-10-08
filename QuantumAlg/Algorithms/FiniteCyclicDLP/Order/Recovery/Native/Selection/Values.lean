/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Correctness
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Soundness
public import QuantumAlg.Components.Classical.FirstAccepted.Option
import all QuantumAlg.Components.Classical.FirstAccepted.Option

/-!
# Pure value of checked known-order recovery selection

The executable selector retains the first accepted candidate.  These value
lemmas identify the selected word and show that a recoverable sample forces
the common secret result regardless of which accepted sample appears first.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open ClassicalRoutines

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Optional contribution of one fully checked sample. -/
public def attemptOption (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2))) :
    Option (CShape.Word (OrderPreparation.width P)) :=
  if attemptAcceptedValue P spec input then some (attemptCandidateValue spec input) else none

/-- Chronological first accepted value of a complete sample vector. -/
public def recoveryValue (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (inputs : Fin count → CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2))) :
    CShape.Value (.option (.unsignedWord (OrderPreparation.width P))) :=
  match (List.ofFn fun index => attemptOption P spec (inputs index)).foldl
      FirstAccepted.retainFirst none with
  | none => CShape.Value.optionNone
  | some value => CShape.Value.optionSome value

private theorem retain_some {α : Type} (values : List (Option α)) (value : α) :
    values.foldl FirstAccepted.retainFirst (some value) = some value := by
  induction values with
  | nil => rfl
  | cons _ tail induction => exact induction

private theorem retained_mem {α : Type} (values : List (Option α)) (value : α)
    (selected : values.foldl FirstAccepted.retainFirst none = some value) :
    some value ∈ values := by
  induction values with
  | nil => cases selected
  | cons head tail induction =>
      cases head with
      | none => exact List.mem_cons_of_mem _ (induction selected)
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
  | cons head tail induction =>
      cases head with
      | none =>
          apply induction
          · exact fun word member => unique word (List.mem_cons_of_mem _ member)
          · exact (List.mem_cons.mp present).resolve_left (by intro impossible; cases impossible)
      | some word =>
          rw [unique word List.mem_cons_self]
          exact retain_some tail value

omit [Fintype G] in
/-- Every returned word belongs to an actually accepted sample. -/
public theorem recoveryValue_some_mem (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (inputs : Fin count → CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (word : CShape.Word (OrderPreparation.width P))
    (selected : recoveryValue P spec count inputs = .optionSome word) :
    ∃ index, attemptAcceptedValue P spec (inputs index) = true ∧
      attemptCandidateValue spec (inputs index) = word := by
  let candidates := List.ofFn fun index => attemptOption P spec (inputs index)
  have returned : candidates.foldl FirstAccepted.retainFirst none = some word := by
    unfold recoveryValue at selected
    change (match candidates.foldl FirstAccepted.retainFirst none with
      | none => CShape.Value.optionNone
      | some value => CShape.Value.optionSome value) = .optionSome word at selected
    cases choice : candidates.foldl FirstAccepted.retainFirst none with
    | none => rw [choice] at selected; cases selected
    | some value =>
        rw [choice] at selected
        exact congrArg some (CShape.Value.optionSome.inj selected)
  obtain ⟨index, member⟩ := List.mem_ofFn.mp (retained_mem candidates word returned)
  by_cases accepted : attemptAcceptedValue P spec (inputs index) = true
  · refine ⟨index, accepted, ?_⟩
    exact Option.some.inj (by
      simpa only [attemptOption, accepted, if_true] using member)
  · simp only [attemptOption, accepted] at member
    cases member

omit [Fintype G] in
/-- Presence of one accepted sample and a common accepted value determine the result. -/
public theorem recoveryValue_eq_some_of_accepted (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (inputs : Fin count → CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (word : CShape.Word (OrderPreparation.width P))
    (present : ∃ index, attemptAcceptedValue P spec (inputs index) = true)
    (unique : ∀ index, attemptAcceptedValue P spec (inputs index) = true →
      attemptCandidateValue spec (inputs index) = word) :
    recoveryValue P spec count inputs = .optionSome word := by
  let candidates := List.ofFn fun index => attemptOption P spec (inputs index)
  have members : ∀ value, some value ∈ candidates → value = word := by
    intro value member
    obtain ⟨index, actual⟩ := List.mem_ofFn.mp member
    by_cases accepted : attemptAcceptedValue P spec (inputs index) = true
    · have same : attemptCandidateValue spec (inputs index) = value :=
        Option.some.inj (by
          simpa only [attemptOption, accepted, if_true] using actual)
      exact same.symm.trans (unique index accepted)
    · simp only [attemptOption, accepted] at actual
      cases actual
  have chosen : some word ∈ candidates := by
    obtain ⟨index, accepted⟩ := present
    apply List.mem_ofFn.mpr
    exact ⟨index, by simp only [attemptOption, accepted, if_true, unique index accepted]⟩
  have result := retained_unique candidates word members chosen
  unfold recoveryValue
  change (match candidates.foldl FirstAccepted.retainFirst none with
    | none => CShape.Value.optionNone
    | some value => CShape.Value.optionSome value) = .optionSome word
  rw [result]

omit [Fintype G] in
/-- Any returned word is the proof-side secret. -/
public theorem recoveryValue_some_eq_secret (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (modulus : spec.modulus = P.order) (count : Nat)
    (inputs : Fin count → CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (word : CShape.Word (OrderPreparation.width P))
    (returned : recoveryValue P spec count inputs = .optionSome word) :
    word = CShape.wordOfNat (OrderPreparation.width P) secret.secret.val := by
  obtain ⟨index, accepted, same⟩ :=
    recoveryValue_some_mem P spec count inputs word returned
  exact same.symm.trans
    (attemptCandidateValue_eq_secret_of_accepted P secret spec modulus (inputs index) accepted)

omit [Fintype G] in
/-- A selected outcome in the vector forces recovery of the proof-side secret. -/
public theorem recoveryValue_selected_samples (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (modulus : spec.modulus = P.order) (count : Nat)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count)
    (present : ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)) :
    recoveryValue P spec count
      (fun index => (OrderEndpoint.rawSamples P count outcomes).get index) =
      .optionSome (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val) := by
  apply recoveryValue_eq_some_of_accepted
  · obtain ⟨index, unit, selected⟩ := present
    refine ⟨index, ?_⟩
    rw [OrderEndpoint.rawSamples_get]
    rw [selected]
    exact attemptAcceptedValue_selected P secret unit spec modulus
  · intro index accepted
    exact attemptCandidateValue_eq_secret_of_accepted P secret spec modulus _ accepted

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
