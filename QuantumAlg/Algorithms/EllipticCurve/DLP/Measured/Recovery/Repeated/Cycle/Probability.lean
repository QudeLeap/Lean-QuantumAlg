/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Selection
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Persistent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure

/-!
# One actual checked ECC attempt contracts the unaccepted mass

The source-derived candidate floor is applied to the same original physical
sampling round and its real unaccepted input fiber. The checked recovery
then contracts the persistent failure event, with arbitrary retained cells,
service history and quantum reference. Public point representations are
assumed only at the actual sampled output where the classical check uses them.
The corrected floor need not be positive for every parameter choice.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
  FiniteCyclicDLP Canonical.Probability
open ClassicalAlgorithms.EllipticCurve ClassicalRoutines.EllipticCurve
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate
attribute [local irreducible] underPersistent persistentCtx

private theorem indicator_decision_weight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (condition : C → Prop)
    (first second : DecidablePred condition) :
    state.effectWeight (fun entry => @ite (Effect R) (condition entry) (first entry)
        (Effect.one R) (Effect.zero R)) =
      state.effectWeight (fun entry => @ite (Effect R) (condition entry) (second entry)
        (Effect.one R) (Effect.zero R)) := by
  cases Subsingleton.elim first second
  rfl

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

def SampledPublicPoints
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) : Prop :=
  ∀ entry,
    0 < (((persistentSamplingRound E fieldTail sameWidth fits odd problem points seed).execute
      Reference state).block entry).mass →
    PointRepresents (Canonical.Layout.curveSpec E)
      (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
    PointRepresents (Canonical.Layout.curveSpec E)
      (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalTargetRef E (orderWidth problem)))) problem.target.toMathlib

def CheckedFailureContracts
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) : Prop :=
  persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    ((persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).execute Reference state) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem) state

/-- Any actual prefix of the original admitted run supplies the public-point
interpretations needed by the following physical sample. No additional
restriction on the original normalized quantum input or reference is imposed. -/
theorem sampledPublicPoints_on_originalPrefix
    (prior : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    SampledPublicPoints E fieldTail sameWidth fits odd problem points seed
      (prior.execute Reference
        (PublicInput.persistentInitialState E (orderWidth problem) problem original)) := by
  unfold SampledPublicPoints
  intro entry positive
  let initial := PublicInput.persistentInitialState E (orderWidth problem) problem original
  let sample := persistentSamplingRound E fieldTail sameWidth fits odd problem points seed
  let fullRecord : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      (Unit × (Store (PublicInput.before E (orderWidth problem)) ×
        (prior.Path × sample.Path))) :=
    (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))
  have fullPositive : 0 < (((prior.seq sample).execute Reference initial).block
      fullRecord).mass := by
    rw [Circuit.execute_seq]
    exact (mapped_positive _ _ _ _).mpr ⟨entry, rfl, positive⟩
  exact PublicInput.persistentProgram_supported_represents E (orderWidth problem)
    problem (prior.seq sample) original fullRecord fullPositive

/-- On the original public-point domain, one named reset/sample/check attempt
contracts actual unaccepted mass by the source-derived corrected candidate
floor. No independence or positive-floor premise is used. -/
theorem persistentCheckedAttempt_failureWeight_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (represents : SampledPublicPoints E fieldTail sameWidth fits odd problem points seed state) :
    CheckedFailureContracts E fieldTail sameWidth fits odd problem points seed nontrivial
      state := by
  unfold SampledPublicPoints at represents
  unfold CheckedFailureContracts
  let terminal := PublicInput.terminal E (orderWidth problem)
  let width := Canonical.Layout.fieldWidth E
  let scalarWidth := orderWidth problem
  let measured := inputLeft (PublicInput.terminal_disjoint E scalarWidth)
    (QubitReadouts.input (exponentMeasurementCells p scalarWidth))
  let sourceSample := samplingRound E fieldTail sameWidth fits odd problem points seed
  let sampleCode := BitWord.selectForCircuit sourceSample
  let localSample := BitWord.selectForCircuit_isLocal sourceSample
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)
  let lower := (problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)
  apply sampledAttempt_failure_weight_le sampleCode localSample
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E scalarWidth)
    (PublicInput.terminalTargetRef E scalarWidth) problem.generator.toMathlib
    problem.target.toMathlib state represents lower
  let rejected := state.selectClassical (fun entry => (entry.1.read
    (.storage (persistentAccepted terminal width scalarWidth).toCStorageRef)).toBool) false
  exact (persistentSamplingRound_candidate_weight_bound E fieldTail sameWidth fits odd
    problem nontrivial points seed addends input rejected).trans_eq
      (indicator_decision_weight _ _ _ _)

/-- The original source-scoped known-order problem itself supplies the proof
witness for one checked attempt's failure contraction. No separate secret
parameter is required by the complete-section protocol. -/
theorem persistentCheckedAttempt_failureWeight_from_knownOrder
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (represents : SampledPublicPoints E fieldTail sameWidth fits odd problem points seed
      state) :
    CheckedFailureContracts E fieldTail sameWidth fits odd problem points seed nontrivial
      state :=
  persistentCheckedAttempt_failureWeight_le E fieldTail sameWidth fits odd problem
    points seed nontrivial addends (SecretInput.ofKnownOrderProblem problem) state represents

/-- Every actual original-input prefix has the one-attempt failure contraction;
the public-point premise is discharged by borrowed preservation on that same
prefix and the subsequent named sampling round. -/
theorem persistentCheckedAttempt_failureWeight_on_originalPrefix
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem)
    (prior : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    CheckedFailureContracts E fieldTail sameWidth fits odd problem points seed nontrivial
      (prior.execute Reference
        (PublicInput.persistentInitialState E (orderWidth problem) problem original)) := by
  exact persistentCheckedAttempt_failureWeight_le E fieldTail sameWidth fits odd
    problem points seed nontrivial addends input _
    (sampledPublicPoints_on_originalPrefix E fieldTail sameWidth fits odd problem
      points seed prior original)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
