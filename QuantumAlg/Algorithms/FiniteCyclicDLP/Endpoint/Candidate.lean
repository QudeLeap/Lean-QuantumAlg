/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Input
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt.Values

/-!
# The original secret in the actual checked candidate

The actual raw inverse and reconstruction flags feed the same group-power
comparison. Injectivity of the original shared encoding makes every accepted
bounded candidate the secret. The original selected-frequency theorem supplies
both flags and that candidate, without restricting the ambient group or its
known order to prime order. The secret remains a mathematical witness.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open ClassicalRoutines.FiniteCyclicDLP CallCountedRecovery.Native

noncomputable section

universe u

variable {G : Type u} [Group G]

private theorem word_injective {width : Nat} (left right : CShape.Word width)
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- The original bounded secret is not truncated by the actual candidate word width. -/
theorem nativeCandidate_secret_toNat (P : KnownOrderProblem G)
    (secret : Probability.SecretInput P) :
    (CShape.wordOfNat (orderWidth P) secret.secret.val).toNat = secret.secret.val := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  rw [CShape.wordOfNat_val]
  exact Nat.mod_eq_of_lt ((ZMod.val_lt secret.secret).trans_le (order_le_fourierModulus P))

/-- Every actually accepted raw candidate equals the original secret under the shared encoding. -/
theorem nativeCandidate_accepted_eq_secret (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P)
    (raw : CShape.Value (.fixedVector (orderWidth P + orderWidth P) (.finite 2)))
    (accepted : attemptAcceptedValue (recoveryParameters P B A) raw (targetValue A) = true) :
    attemptCandidateValue (recoveryParameters P B A) raw =
      CShape.wordOfNat (orderWidth P) secret.secret.val := by
  dsimp only [recoveryParameters] at *
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have equality := (Bool.and_eq_true_iff.mp accepted).2
  have encoded :
      A.recovery.encode
          (P.generator ^ (attemptCandidateValue (recoveryParameters P B A) raw).toNat) =
        targetValue A := word_injective _ _ (of_decide_eq_true equality)
  have powers := recovery_encode_injective A encoded
  have samePower :
      P.generator ^ (attemptCandidateValue (recoveryParameters P B A) raw).toNat =
        P.generator ^ secret.secret.val := powers.trans secret.target_eq_generator_pow.symm
  have sameResidue := pow_inj_mod.mp samePower
  have bounded := groupAttempt_candidate_lt (recoveryParameters P B A) raw
  change (attemptCandidateValue (recoveryParameters P B A) raw).toNat < P.order at bounded
  dsimp only [recoveryParameters] at bounded sameResidue
  apply word_injective
  rw [nativeCandidate_secret_toNat]
  simpa only [← P.order_eq_orderOf, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (ZMod.val_lt secret.secret)] using sameResidue

/-- The original selected-frequency family passes both raw flags and the actual group test.

The input equality connects two mathematical observations of the same raw
sample. It is supplied by the endpoint's reversible finite-cell observation,
not by a runtime candidate or success certificate.
-/
theorem nativeCandidate_selected (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) (unit : (ZMod P.order)ˣ)
    (raw : CShape.Value (.fixedVector (orderWidth P + orderWidth P) (.finite 2)))
    (selected : RawRecovery.Native.preparationInput raw =
      Probability.RecoveryBridge.selectedRawInput P secret unit) :
    attemptCandidateValue (recoveryParameters P B A) raw =
        CShape.wordOfNat (orderWidth P) secret.secret.val ∧
      attemptAcceptedValue (recoveryParameters P B A) raw (targetValue A) = true := by
  dsimp only [recoveryParameters] at *
  obtain ⟨output, actual, candidate, verified⟩ :=
    Probability.RecoveryBridge.outputOf_selectedRawInput_recovers P secret unit
      (recoveryParameters P B A).spec rfl
  have values : RawRecovery.outputCells (recoveryParameters P B A).spec
      (RawRecovery.Native.preparationInput raw) =
      .product (.bit true)
        (.product (CShape.wordOfNat (orderWidth P) secret.secret.val) (.bit true)) := by
    erw [selected, RawRecovery.outputCells, actual]
    dsimp only
    simp only [candidate, verified, recoveryParameters]
  have chosen : attemptCandidateValue (recoveryParameters P B A) raw =
      CShape.wordOfNat (orderWidth P) secret.secret.val := by
    unfold attemptCandidateValue
    rw [values]
    rfl
  refine ⟨chosen, ?_⟩
  unfold attemptAcceptedValue
  erw [values, chosen]
  dsimp only [recoveryParameters, CShape.Value.first, CShape.Value.second, CShape.Value.toBool]
  simp only [Bool.true_and, nativeCandidate_secret_toNat]
  rw [secret.target_eq_generator_pow]
  simp [targetValue]

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
