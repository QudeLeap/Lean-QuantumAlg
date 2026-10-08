/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Fiber
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure

/-!
# Candidate floor in the checked recovery's exact event interface

The accepted candidate event and the actual selected local circuit are
spelled exactly as required by the generic checked-recovery contraction law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The rejected fiber's candidate event has the generic checker's exact
shape, with the unchanged selected local readout and no leading reset. -/
theorem persistentSamplingReadout_candidate_weight_for_checkedRecovery
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H))
    (supported : ∀ basis, basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed →
        state.quantumMarginal.matrix basis basis = 0) :
    let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
    let raw := samplingReadout E fieldTail odd problem points
    let selected := BitWord.selectForCircuit raw
    let localSample := BitWord.selectForCircuit_isLocal raw
      (samplingReadout_isLocal E fieldTail odd problem points)
    let rejected := state.selectClassical (fun entry => (entry.1.read
      (.storage (persistentAccepted (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef)).toBool) false
    rejected.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((underPersistent selected localSample (Canonical.Layout.fieldWidth E)
        (orderWidth problem)).execute Reference rejected).effectWeight (fun entry =>
          if SampleAccepted (Canonical.Layout.curveSpec E)
            (recoveryModulusSpec problem nontrivial)
            problem.generator.toMathlib problem.target.toMathlib
            (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
              (orderWidth problem) (rawRecoveryInput problem measured))) then
            Effect.one ((persistentCtx (PublicInput.terminal E (orderWidth problem))
              (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)
          else Effect.zero ((persistentCtx (PublicInput.terminal E (orderWidth problem))
              (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)) := by
  let raw := samplingReadout E fieldTail odd problem points
  let selected := BitWord.selectForCircuit raw
  have localSample : selected.IsLocal := BitWord.selectForCircuit_isLocal raw
    (samplingReadout_isLocal E fieldTail odd problem points)
  have floor := persistentSamplingReadout_candidate_weight_on_rejectedFiber E
    fieldTail sameWidth fits odd problem points seed nontrivial addends state supported
  unfold SupportedReadoutCandidateFloor at floor
  have sameCode :
      persistentSamplingReadout E fieldTail odd problem points =
        underPersistent selected localSample (Canonical.Layout.fieldWidth E)
          (orderWidth problem) := rfl
  rw [sameCode] at floor
  simpa only [persistentReadoutCandidateEffects] using floor

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
