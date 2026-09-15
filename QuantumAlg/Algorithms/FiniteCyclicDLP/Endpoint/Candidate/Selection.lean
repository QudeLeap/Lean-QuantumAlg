/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Candidate
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Samples
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection.Values

/-!
# The original selected sample forces the actual first-success result

All accepted candidates equal the same secret under the original shared
encoding. Therefore any selected-frequency sample forces the actual ordered
recovery fold to return that secret, even if an earlier sample already
accepted. Every sample still executes; no stopping rule is introduced.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open ClassicalRoutines.FiniteCyclicDLP CallCountedRecovery.Native
open GateLevelAttempt.Native (sampleWidth)

noncomputable section

universe u

variable {G : Type u} [Group G]

private theorem preparation_rawSample (P : KnownOrderProblem G)
    (outcome : Fin (sampleWidth P) → Bool) :
    RawRecovery.Native.preparationInput (rawSample P outcome) = .bits outcome := by
  change CShape.Value.bits (GateLevelAttempt.Native.observedOutcome P (rawSample P outcome)) = _
  rw [observed_rawSample]
  rfl

/-- Any word returned by the actual original fold is the original secret. -/
theorem nativeRecovery_some_eq_secret (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) (count : Nat)
    (inputs : Fin count → CShape.Value (.fixedVector (orderWidth P + orderWidth P) (.finite 2)))
    (word : CShape.Word (orderWidth P))
    (returned : groupRecoveryValue (recoveryParameters P B A) count inputs (targetValue A) =
      .optionSome word) : word = CShape.wordOfNat (orderWidth P) secret.secret.val := by
  obtain ⟨index, accepted, same⟩ := groupRecoveryValue_some_mem
    (recoveryParameters P B A) count inputs (targetValue A) word returned
  exact same.symm.trans (nativeCandidate_accepted_eq_secret P B A secret (inputs index) accepted)

/-- A selected original sample makes the same complete recovery fold return the secret.

The selected event is a proof-side subset of all raw outcomes. The input
samples, both raw flags, group tests and first-success selector remain the
actual executable ones, with no new initialization or success premise.
-/
theorem nativeRecovery_selected_samples (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) (count : Nat)
    (outcomes : List.Vector (Fin (sampleWidth P) → Bool) count)
    (present : ∃ index, Probability.SelectedRawOutcome P secret (outcomes.get index)) :
    groupRecoveryValue (recoveryParameters P B A) count
      (fun index => (rawSamples P count outcomes).get index) (targetValue A) =
      .optionSome (CShape.wordOfNat (orderWidth P) secret.secret.val) := by
  apply groupRecoveryValue_eq_some_of_accepted
  · obtain ⟨index, unit, selected⟩ := present
    refine ⟨index, (nativeCandidate_selected P B A secret unit
      ((rawSamples P count outcomes).get index) ?_).2⟩
    change RawRecovery.Native.preparationInput (rawSample P (outcomes.get index)) = _
    rw [preparation_rawSample, selected]
    rfl
  · intro index accepted
    exact nativeCandidate_accepted_eq_secret P B A secret
      ((rawSamples P count outcomes).get index) accepted

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
