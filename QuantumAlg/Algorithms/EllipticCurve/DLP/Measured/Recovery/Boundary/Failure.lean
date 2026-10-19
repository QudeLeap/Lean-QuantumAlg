/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability.Finite
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Loop

/-!
# Unnormalized first-attempt contraction on the native original-input prefix

The original coefficient, including its exceptional-error term, multiplies
the actual prior failure weight. It is not replaced by a normalized branch
probability or a weaker absolute bound. Every original Input and arbitrary
external Reference is retained by the public carrier's prescribed input map.

The proof uses the same complete candidate floor and original checker. No
positivity assumption on that corrected floor, repeated-reset assumption,
initialized caller bank or point-representation premise is added.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP Canonical.Probability
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open GenericPointAddition.InPlace

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

set_option maxHeartbeats 400000 in
-- Checking the complete store observation bridge exceeded the default finite budget.
private lemma persistentFailureWeight_seq
    {origin middle ctx : RuntimeCtx .quantum} {width scalarWidth : Nat}
    (prior : Circuit Model origin middle)
    (code : Circuit Model middle (persistentCtx ctx width scalarWidth))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State origin Reference (Unit × History)) :
    persistentFailureWeight (model := Model) (ctx := ctx)
      (width := width) (scalarWidth := scalarWidth)
      ((prior.seq code).execute environment Reference state) =
      persistentFailureWeight (model := Model) (ctx := ctx)
        (width := width) (scalarWidth := scalarWidth)
        (code.execute environment Reference (prior.execute environment Reference state)) := by
  let : DecidableEq Bool := Classical.decEq Bool
  let effects : Store (persistentCtx ctx width scalarWidth) →
      Effect ((persistentCtx ctx width scalarWidth).register.prod Reference) := fun stored =>
    if (stored.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        false then
      Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
    else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)
  have observed := storedWeight_seq (environment := environment) (model := Model)
    (Reference := Reference) (H := History)
    prior code state effects
  unfold persistentFailureWeight
  conv =>
    lhs
    arg 2
    equals (fun record => effects record.1) =>
      funext record
      by_cases rejected : (record.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false
      · simp only [effects, if_pos rejected]
      · simp only [effects, if_neg rejected]
  conv =>
    rhs
    arg 2
    equals (fun record => effects record.1) =>
      funext record
      by_cases rejected : (record.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false
      · simp only [effects, if_pos rejected]
      · simp only [effects, if_neg rejected]
  exact observed

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

set_option maxHeartbeats 800000 in
-- Checking the complete prefix statement exceeded the default finite budget.
/-- Any actual native prefix contracts its full unnormalized failure state by the original factor.
-/
lemma attempt_failureWeight_on_prefix
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (prior : Circuit Model (Recovery.PublicInput.frame E (orderWidth problem)) (sectionCtx E
      problem)) :
    persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth
      problem))
      (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((attempt E fieldTail problem points seed problem.order
        (Semantics.radixUnit p fieldTail.succ odd) nontrivial).execute environment Reference
          (prior.execute environment Reference
            (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original))) ≤
      (1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
        persistentFailureWeight (model := Model)
          (ctx := Recovery.PublicInput.context E (orderWidth problem))
          (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
          (prior.execute environment Reference
            (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem
              original)) := by
  let sampleCode : Circuit Model (Recovery.PublicInput.context E (orderWidth problem))
      (Recovery.PublicInput.context E (orderWidth problem)) false :=
    round E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd)
  let initial : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (Unit × Store (Recovery.PublicInput.frame E (orderWidth problem))) :=
    Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original
  let lower : ℝ := (problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)
  let stepCode : Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
    sampledAttempt sampleCode (ECDLP.Canonical.Layout.curveSpec E)
      (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem))
  have contracted := sampledAttempt_failure_on_prefix (environment := environment) (model := Model)
    (origin := Recovery.PublicInput.frame E (orderWidth problem))
    (ctx := Recovery.PublicInput.context E (orderWidth problem))
    (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (Reference := Reference) (H := Store (Recovery.PublicInput.frame E (orderWidth problem)))
    sampleCode (ECDLP.Canonical.Layout.curveSpec E)
    (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem))
    problem.generator.toMathlib problem.target.toMathlib initial
    (fun priorCode => Recovery.PublicInput.Support.persistentProgram_supported_represents E
      (orderWidth problem) problem priorCode original) lower
    (fun History _ state => by
      have floor := CandidateProbability.actual_persistent_round_candidate_weight_bound
        (environment := environment)
        (Reference := Reference) (History := History)
        E fieldTail odd problem points seed sameWidth fits nontrivial addends input state
      refine floor.trans_eq ?_
      exact FiniteSuccess.indicator_decision_weight _ _ _ _) prior
  have observed := persistentFailureWeight_seq (environment := environment)
    (ctx := Recovery.PublicInput.context E (orderWidth problem))
    (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (Reference := Reference)
    (History := Store (Recovery.PublicInput.frame E (orderWidth problem)))
    prior stepCode initial
  exact observed.symm.trans_le contracted

set_option maxHeartbeats 400000 in
-- Checking the complete first-attempt statement exceeded the default finite budget.
/-- The actual one-time allocation and seven-cell initialization specialize that full bound. -/
lemma firstAttempt_failureWeight_le
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth
      problem))
      (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((attempt E fieldTail problem points seed problem.order
        (Semantics.radixUnit p fieldTail.succ odd) nontrivial).execute environment Reference
          ((«prefix» E problem).execute environment Reference
            (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original))) ≤
      (1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
        persistentFailureWeight (model := Model)
          (ctx := Recovery.PublicInput.context E (orderWidth problem))
          (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
          ((«prefix» E problem).execute environment Reference
            (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original)) :=
  attempt_failureWeight_on_prefix E fieldTail odd problem points seed sameWidth fits nontrivial
    addends input original («prefix» E problem)

set_option maxHeartbeats 400000 in
-- Checking the complete canonical-instance statement exceeded the default finite budget.
/-- Canonical instances supply their secret witness internally, as in the original obligation. -/
lemma algorithm_firstAttempt_failureWeight_le
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend
        (orderWidth (ECDLP.Canonical.problem I))
        (ECDLP.Canonical.problem I).generator (ECDLP.Canonical.problem I).target)
    {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth (ECDLP.Canonical.problem I)))
      Reference) :
    let problem := ECDLP.Canonical.problem I
    let initial := Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original
    persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth
      problem))
      (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((attempt E fieldTail problem points seed problem.order
        (Semantics.radixUnit p fieldTail.succ odd) I.subgroupOrder_prime.two_le).execute
          environment Reference
          ((«prefix» E problem).execute environment Reference initial)) ≤
      (1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
        persistentFailureWeight (model := Model)
          (ctx := Recovery.PublicInput.context E (orderWidth problem))
          (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
          ((«prefix» E problem).execute environment Reference initial) :=
  firstAttempt_failureWeight_le E fieldTail odd (ECDLP.Canonical.problem I) points seed
    sameWidth fits I.subgroupOrder_prime.two_le addends
    ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I⟩ original

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
