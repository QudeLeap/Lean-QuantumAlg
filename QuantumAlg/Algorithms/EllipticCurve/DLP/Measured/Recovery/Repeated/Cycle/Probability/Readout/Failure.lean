/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Fiber
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Validity
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Effects

/-!
# The actual reset-free reused ECC sample and check

The candidate floor is applied on the same unaccepted input fiber used by
checked recovery. This contracts actual unaccepted mass after the unchanged
sampling/readout and check, before the section's trailing reset.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ClassicalAlgorithms.EllipticCurve ClassicalRoutines.EllipticCurve
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate
attribute [local irreducible] underPersistent

private theorem if_decider_irrel {α : Sort _} (condition : Prop)
    (first second : Decidable condition) (yes no : α) :
    @ite α condition first yes no = @ite α condition second yes no := by
  cases first <;> cases second <;> simp_all

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The failure event after the unchanged reused readout and checked recovery,
before the charged trailing reset. -/
def CheckedReadoutFailureContracts
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H)) : Prop :=
  persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (((persistentSamplingReadout E fieldTail odd problem points).seq
      (persistentCheckedRecovery E problem nontrivial)).execute Reference state) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem) state

/-- The same contraction before identifying the generic checked attempt with
the named reused `S;C` circuit. -/
def CheckedReadoutSampledFailureContracts
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H)) : Prop :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let raw := samplingReadout E fieldTail odd problem points
  let selected := BitWord.selectForCircuit raw
  let localSample := BitWord.selectForCircuit_isLocal raw
    (samplingReadout_isLocal E fieldTail odd problem points)
  persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    ((sampledAttempt selected localSample (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) (rawRecoveryInput problem measured)
      (PublicInput.terminalBaseRef E (orderWidth problem))
      (PublicInput.terminalTargetRef E (orderWidth problem))).execute Reference state) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem) state

/-- The real reused readout/check body contracts failure mass on any
supported public-point state. No leading reset or independence is assumed. -/
theorem persistentCheckedReadout_sampledFailureWeight_of_support
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
    CheckedReadoutSampledFailureContracts E fieldTail odd problem points seed nontrivial
      state := by
  unfold CheckedReadoutSampledFailureContracts
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let raw := samplingReadout E fieldTail odd problem points
  let selected := BitWord.selectForCircuit raw
  have localSample : selected.IsLocal := BitWord.selectForCircuit_isLocal raw
    (samplingReadout_isLocal E fieldTail odd problem points)
  have sameCode :
      persistentSamplingReadout E fieldTail odd problem points =
        underPersistent selected localSample (Canonical.Layout.fieldWidth E)
          (orderWidth problem) := rfl
  have represents := persistentSamplingReadout_points_of_validity E fieldTail odd
    problem points state valid
  rw [sameCode] at represents
  have floor := persistentSamplingReadout_candidate_weight_on_rejectedFiber E
    fieldTail sameWidth fits odd problem points seed nontrivial addends state supported
  unfold SupportedReadoutCandidateFloor at floor
  rw [sameCode] at floor
  refine sampledAttempt_failure_weight_le_of_effects
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    selected localSample
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) problem.generator.toMathlib
    problem.target.toMathlib state ?_
    ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))
    (persistentReadoutCandidateEffects E problem nontrivial) ?_ ?_
  · exact represents
  · intro entry
    simp only [persistentReadoutCandidateEffects, measured]
    apply if_decider_irrel
  · exact floor

/-- The named actual reused `S;C` body is exactly the generic checked attempt
instantiated with the original selected readout and recovery inputs. -/
theorem persistentCheckedReadout_body_eq_sampledAttempt :
    (persistentSamplingReadout E fieldTail odd problem points).seq
      (persistentCheckedRecovery E problem nontrivial) =
    let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
    let raw := samplingReadout E fieldTail odd problem points
    sampledAttempt (BitWord.selectForCircuit raw)
      (BitWord.selectForCircuit_isLocal raw
        (samplingReadout_isLocal E fieldTail odd problem points))
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
      (PublicInput.terminalTargetRef E (orderWidth problem)) := rfl

/-- The generic contraction reaches the named actual reused `S;C` circuit. -/
theorem persistentCheckedReadout_failureWeight_of_support
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
    CheckedReadoutFailureContracts E fieldTail odd problem points seed nontrivial state := by
  have core := persistentCheckedReadout_sampledFailureWeight_of_support E fieldTail
    sameWidth fits odd problem points seed nontrivial addends state supported valid
  unfold CheckedReadoutFailureContracts
  unfold CheckedReadoutSampledFailureContracts at core
  rw [persistentCheckedReadout_body_eq_sampledAttempt E fieldTail odd problem points
    nontrivial]
  exact core

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
