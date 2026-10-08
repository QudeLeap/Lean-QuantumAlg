/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Readout
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.History

/-!
# Failure contraction for the actual first and reused ECC sections

The physical trailing reset preserves the failure mass after the real
readout/check body. The completed reused section therefore has the same
source-derived contraction. The first section uses the original leading
reset/sample/check attempt and its proven path-reassociation certificate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The unchanged `S;C;R` reused section contracts its actual unaccepted
mass on every supported, public-point-valid input state. -/
theorem reusedCheckedSection_failureWeight_of_support
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H))
    (supported : ∀ basis, basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed →
        state.quantumMarginal.matrix basis basis = 0)
    (valid : ∀ entry, 0 < (state.block entry).mass →
      CheckedSelectionValid E problem entry.1) :
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).execute Reference state) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      state := by
  have contraction := persistentCheckedReadout_failureWeight_of_support E fieldTail
    sameWidth fits odd problem points seed nontrivial addends state supported valid
  unfold CheckedReadoutFailureContracts at contraction
  unfold reusedCheckedSectionCode
  rw [Circuit.execute_seq, persistentFailureWeight_mapHistory,
    persistentSamplingReset_failureWeight E fieldTail sameWidth fits problem seed]
  exact contraction

/-- Admission to the independent section input domain and its established
physical seed suffice for the completed reused section's failure bound. -/
theorem reusedCheckedSection_failureWeight_on_admittedInput
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      input.localState) :
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).execute Reference (State.skip input.state)) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      (State.skip input.state) := by
  apply reusedCheckedSection_failureWeight_of_support E fieldTail sameWidth fits odd
    problem points seed nontrivial addends (State.skip input.state)
  · intro basis outside
    rw [State.skip_quantumMarginal]
    exact checkedSectionSeededInitialization_jointSupport E fieldTail sameWidth fits
      problem seed input seeded basis outside
  · exact checkedSection_entered_validity E problem input valid

/-- The unchanged `R;S;C;R` first section contracts failure mass on every
admitted joint input, including arbitrary incoming quantum/reference state. -/
theorem firstCheckedSection_failureWeight_on_admittedInput
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState) :
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).execute Reference (State.skip input.state)) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      (State.skip input.state) := by
  have contraction := persistentCheckedAttempt_failureWeight_on_admittedInput E fieldTail
    sameWidth fits odd problem points seed nontrivial addends input valid
  unfold CheckedFailureContracts at contraction
  have sameMass :
      persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (ctx := PublicInput.terminal E (orderWidth problem))
        (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
        ((persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
          nontrivial).execute Reference (State.skip input.state)) =
      persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (ctx := PublicInput.terminal E (orderWidth problem))
        (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
        (((persistentSamplingReset E fieldTail sameWidth fits problem seed).seq
          ((persistentSamplingReadout E fieldTail odd problem points).seq
            (persistentCheckedRecovery E problem nontrivial))).execute Reference
            (State.skip input.state)) := by
    rw [(persistentCheckedAttempt_operationalEquiv E fieldTail sameWidth fits odd
      problem points seed nontrivial).execute Reference (State.skip input.state),
      persistentFailureWeight_mapHistory]
  unfold firstCheckedSectionCode
  rw [Circuit.execute_seq, persistentFailureWeight_mapHistory,
    persistentSamplingReset_failureWeight E fieldTail sameWidth fits problem seed,
    ← sameMass]
  exact contraction

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
