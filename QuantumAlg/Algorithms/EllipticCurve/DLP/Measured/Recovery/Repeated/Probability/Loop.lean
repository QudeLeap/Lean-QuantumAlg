/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Persistent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.FailureBudget
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Boundary
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect

/-!
# Actual repeated ECDLP failure probability

The real first-success latches begin unaccepted. The same complete state
passes through every reset, sample, checked recovery and selection. Its
failure mass contracts along those actual prefixes, and the final option
pack reads precisely that mass. The original exceptional error remains in
the geometric coefficient, with no independence or positive-floor premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] underPersistent retainPersistent

private theorem indicator_decision_weight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (condition : C → Prop)
    (first second : DecidablePred condition) :
    state.effectWeight (fun entry => @ite (Effect R) (condition entry) (first entry)
        (Effect.one R) (Effect.zero R)) =
      state.effectWeight (fun entry => @ite (Effect R) (condition entry) (second entry)
        (Effect.one R) (Effect.zero R)) := by
  cases Subsingleton.elim first second
  rfl

private theorem four_stage_weight {kind : ProblemKind}
    {origin first second final result : RuntimeCtx kind}
    (setup : Circuit origin first) (allocation : Circuit first second)
    (body : Circuit second final) (packing : Circuit final result)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (effects : Store result → Effect (result.register.prod Reference)) :
    ((setup.seq ((allocation.seq body).seq packing)).execute Reference initial).effectWeight
        (fun entry => effects entry.1) =
      (packing.execute Reference (((setup.seq allocation).seq body).execute
        Reference initial)).effectWeight (fun entry => effects entry.1) := by
  simp only [Circuit.execute_seq, Circuit.execute_mapHistory, State.effectWeight_mapHistory]

private theorem initialized_failure_weight {kind : ProblemKind}
    {origin ctx : RuntimeCtx kind} (setup : Circuit origin ctx) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
        ((setup.seq (retainPersistent ctx width scalarWidth)).execute Reference initial) =
      initial.mass := by
  exact (storedWeight_seq setup (retainPersistent ctx width scalarWidth) initial
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))).trans
    ((retainPersistent_failure_weight width scalarWidth (setup.execute Reference initial)).trans
      (setup.execute_mass Reference initial))

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual final None probability obeys the original complete-floor geometric bound. -/
theorem exponentRepeatedRun_none_probability_le
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).outputDistribution
        (PublicInput.initialInput E (orderWidth problem) problem original)
          .optionNone ≤
      ENNReal.ofReal ((1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed))) ^ count) := by
  let width := Canonical.Layout.fieldWidth E
  let scalarWidth := orderWidth problem
  let terminal := PublicInput.terminal E scalarWidth
  let measured := inputLeft (PublicInput.terminal_disjoint E scalarWidth)
    (QubitReadouts.input (exponentMeasurementCells p scalarWidth))
  let sample := rawRecoveryInput problem measured
  let base := PublicInput.terminalBaseRef E scalarWidth
  let target := PublicInput.terminalTargetRef E scalarWidth
  let curve := Canonical.Layout.curveSpec E
  let modulus := recoveryModulusSpec problem nontrivial
  let sampleCode := samplingRound E fieldTail sameWidth fits odd problem points seed
  let localSample := samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed
  let setup := (PublicInput.initializeWork E scalarWidth).seq
    (PublicInput.allocateTerminal E scalarWidth)
  let allocation := retainPersistent terminal width scalarWidth
  let body := sampledAttempts sampleCode localSample count curve modulus sample base target
  let packing := packBatchResult terminal width scalarWidth
  let supplied := PublicInput.initialInput E scalarWidth problem original
  let initial := supplied.state.mapClassical (fun store => (store, store))
  let lower := (problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)
  have normalized : initial.mass = 1 :=
    (supplied.state.mapClassical_mass _).trans supplied.normalized
  have contracted : persistentFailureWeight
      (ctx := terminal) (width := width) (scalarWidth := scalarWidth)
      (((setup.seq allocation).seq body).execute Reference initial) ≤
      (1 - lower) ^ count := by
    have geometric := sampledAttempts_failure_weight_le_on_prefix sampleCode localSample count
      curve modulus sample base target problem.generator.toMathlib problem.target.toMathlib
      initial (fun priorCode => PublicInput.persistentProgram_supported_represents E scalarWidth
        problem priorCode original) lower (samplingCandidateFloor_le_one problem points seed)
      (fun K _ state => (persistentSamplingRound_candidate_weight_bound E fieldTail sameWidth fits
        odd problem nontrivial points seed addends input state).trans_eq
          (indicator_decision_weight _ _ _ _)) (setup.seq allocation)
    rw [initialized_failure_weight, normalized, mul_one] at geometric
    exact geometric
  have packed := packBatchResult_none_weight width scalarWidth
    (((setup.seq allocation).seq body).execute Reference initial)
  have completed := (four_stage_weight setup allocation body packing initial
    (fun store => if store.read (batchResultRead terminal width scalarWidth) = .optionNone then
      Effect.one ((batchResultCtx terminal width scalarWidth).register.prod Reference)
    else Effect.zero ((batchResultCtx terminal width scalarWidth).register.prod Reference))).trans
      packed
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  exact ENNReal.ofReal_le_ofReal (completed.trans_le contracted)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
