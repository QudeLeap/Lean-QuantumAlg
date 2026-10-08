/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Failure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Seeded

/-!
# Failure contraction on every admitted reused ECC section input

The independent public-point domain and previously established physical seed
discharge the two hypotheses of the actual reset-free readout/check bound.
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

/-- The actual reused readout/check contracts failure mass on every admitted
joint input, with no separate input-state or secret-witness premise. -/
theorem persistentCheckedReadout_failureWeight_on_admittedInput
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
    CheckedReadoutFailureContracts E fieldTail odd problem points seed nontrivial
      (State.skip input.state) := by
  apply persistentCheckedReadout_failureWeight_of_support E fieldTail sameWidth fits odd
    problem points seed nontrivial addends (State.skip input.state)
  · intro basis outside
    rw [State.skip_quantumMarginal]
    exact checkedSectionSeededInitialization_jointSupport E fieldTail sameWidth fits
      problem seed input seeded basis outside
  · exact checkedSection_entered_validity E problem input valid

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
