/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional
import all QuantumAlg.Util.PMF

/-!
# The chronological first-success law for independent optional words

These mathematical laws use the same optional update as the actual selector.
An empty final result means every candidate was empty. Independent candidates
therefore give the exact power of their one-candidate empty probability,
including a zero-length list. A populated result is one of the original
candidates, so any property valid throughout their support is retained.
The circuit-to-distribution equation remains a separate execution obligation.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Distribution

noncomputable section

variable {width : Nat}

/-- Independent mathematical specification of chronological first-success selection. -/
def firstValue (values : List (CShape.option (.unsignedWord width)).Value) :
    (CShape.option (.unsignedWord width)).Value :=
  values.foldl Optional.retainValue .optionNone

/-- Once selected, an existing word survives every remaining chronological candidate. -/
lemma foldl_some (values : List (CShape.option (.unsignedWord width)).Value)
    (word : CShape.Word width) :
    values.foldl Optional.retainValue (.optionSome word) = .optionSome word := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact ih

/-- The first populated head wins; an empty head leaves the original suffix order intact. -/
lemma firstValue_cons (head : (CShape.option (.unsignedWord width)).Value)
    (tail : List (CShape.option (.unsignedWord width)).Value) :
    firstValue (head :: tail) = Optional.retainValue head (firstValue tail) := by
  cases head with
  | optionNone => rfl
  | optionSome word => exact foldl_some tail word

/-- The selector is empty exactly when every original chronological candidate is empty. -/
lemma firstValue_eq_none_iff (values : List (CShape.option (.unsignedWord width)).Value) :
    firstValue values = .optionNone ↔ ∀ value ∈ values, value = .optionNone := by
  induction values with
  | nil => simp [firstValue]
  | cons head tail ih =>
      rw [firstValue_cons]
      cases head <;> simp [Optional.retainValue, ih]

/-- Every populated selected word is one of the actual original candidates. -/
lemma firstValue_some_mem (values : List (CShape.option (.unsignedWord width)).Value)
    (word : CShape.Word width) (selected : firstValue values = .optionSome word) :
    CShape.Value.optionSome word ∈ values := by
  induction values with
  | nil => cases selected
  | cons head tail ih =>
      rw [firstValue_cons] at selected
      cases head with
      | optionNone => exact List.mem_cons_of_mem _ (ih selected)
      | optionSome earlier =>
          have same : earlier = word := CShape.Value.optionSome.inj selected
          subst earlier
          exact List.mem_cons_self

/-- Pure first-success distribution of exactly the requested number of independent candidates. -/
def selectedDistribution (distribution : PMF (CShape.option (.unsignedWord width)).Value)
    (count : Nat) : PMF (CShape.option (.unsignedWord width)).Value :=
  (PMF.independentReplicateVector distribution count).map
    (fun values => firstValue values.toList)

/-- The exact empty-output probability is the one-candidate empty probability to the count. -/
lemma selectedDistribution_none
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat) :
    selectedDistribution distribution count .optionNone = distribution .optionNone ^ count := by
  rw [← PMF.toOuterMeasure_apply_singleton, selectedDistribution, PMF.toOuterMeasure_map_apply]
  have emptySet :
      (fun values : List.Vector (CShape.option (.unsignedWord width)).Value count =>
        firstValue values.toList) ⁻¹' {CShape.Value.optionNone} =
      {values | ∀ value ∈ values.toList, value = .optionNone} := by
    ext values
    exact firstValue_eq_none_iff values.toList
  rw [emptySet, PMF.independentReplicateVector_allEventProbability_eq]
  rw [Set.ofPred_eq_eq_singleton, PMF.toOuterMeasure_apply_singleton]

/-- A one-candidate failure ceiling gives the matching finite first-success power bound. -/
lemma selectedDistribution_none_le
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (failure : ENNReal) (bounded : distribution .optionNone ≤ failure) :
    selectedDistribution distribution count .optionNone ≤ failure ^ count := by
  rw [selectedDistribution_none]
  exact pow_le_pow_left' bounded count

/-- A selected populated word belongs to the one-candidate support. -/
lemma selectedDistribution_some_support
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (word : CShape.Word width)
    (supported : CShape.Value.optionSome word ∈
      (selectedDistribution distribution count).support) :
    CShape.Value.optionSome word ∈ distribution.support := by
  rw [selectedDistribution, PMF.mem_support_map_iff] at supported
  rcases supported with ⟨values, supported, selected⟩
  have listSupported : values.toList ∈
      (PMF.independentReplicate distribution count).support := by
    rw [← PMF.independentReplicateVector_toList, PMF.mem_support_map_iff]
    exact ⟨values, supported, rfl⟩
  exact PMF.independentReplicate_support_forall distribution count listSupported _
    (firstValue_some_mem values.toList word selected)

/-- Any support-level property of populated input words survives chronological selection. -/
lemma selectedDistribution_some_safe
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (property : CShape.Word width → Prop)
    (safe : ∀ word, CShape.Value.optionSome word ∈ distribution.support → property word)
    (word : CShape.Word width)
    (supported : CShape.Value.optionSome word ∈
      (selectedDistribution distribution count).support) : property word :=
  safe word (selectedDistribution_some_support distribution count word supported)

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Distribution
