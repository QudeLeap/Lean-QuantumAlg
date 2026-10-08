/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout
import all QuantumAlg.Core.Execution.Classical.BasisSupport

/-!
# Reused ECC readout on the actual rejected fiber

Classical rejection retains the original quantum support and its unnormalized
mass. The source candidate floor therefore applies to the same physical
fiber that the checked recovery subsequently tests.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- Filtering the retained accepted bit cannot create a nonseeded quantum
basis component, even with arbitrary classical history and reference. -/
theorem rejectedReadoutFiber_basisSupport
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H))
    (supported : ∀ basis, basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed →
        state.quantumMarginal.matrix basis basis = 0)
    (basis) (outside : basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed) :
    (state.selectClassical (fun entry => (entry.1.read
      (.storage (persistentAccepted (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef)).toBool)
      false).quantumMarginal.matrix basis basis = 0 := by
  exact ExecutionState.filterClassical_diagonal_zero state _ basis
    (supported basis outside)

/-- The original corrected candidate floor holds on the actual unaccepted
fiber of every supported reused-section input. -/
theorem persistentSamplingReadout_candidate_weight_on_rejectedFiber
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
    let rejected := state.selectClassical (fun entry => (entry.1.read
      (.storage (persistentAccepted (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef)).toBool) false
    SupportedReadoutCandidateFloor E fieldTail odd problem points seed nontrivial rejected := by
  dsimp only
  apply persistentSamplingReadout_candidate_weight_of_support E fieldTail sameWidth fits odd
    problem points seed nontrivial addends (SecretInput.ofKnownOrderProblem problem)
  exact rejectedReadoutFiber_basisSupport E fieldTail sameWidth fits problem seed
    state supported

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
