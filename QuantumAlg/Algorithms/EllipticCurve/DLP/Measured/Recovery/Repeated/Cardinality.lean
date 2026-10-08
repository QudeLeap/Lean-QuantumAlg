/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cardinality.Round
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Cardinality

/-!
# Actual repeated-sampling and original classical event ceiling

True reset traces contain at most two events per original physical wire. Each round
then incurs the original quantum sampling/readout allowance and the original
complete classical recovery ceiling. The literal zero preparations, fixed X
load and selector preparation occur once, as does the final option pack. All
iteration counts, including zero, describe
the same actual reused-workspace program without a success or input promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP ConcreteCircuitAccess MeasuredUncompute
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- Each round retains the original complete classical recovery ceiling in its event count. -/
theorem exponentRepeatedRun_eventCount_le (nontrivial : 2 ≤ problem.order) (count : Nat)
    (path : (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).Path) :
    ((exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).eventTrace path).length ≤
        (Allocation.initializationTrace p (2 * orderWidth problem)).length +
          count * (samplingRoundEventBound E problem +
          (42 * orderWidth problem +
            orderWidth problem * (248 * Canonical.Layout.fieldWidth E + 644) + 119)) + 1 := by
  let initial := exponentRepeatedInitial E problem
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  let tail := repeatedTailRun E fieldTail sameWidth fits odd problem points seed
    nontrivial count
  change ((BitWord.selectForCircuit initial).eventTrace path.1 ++
    tail.code.eventTrace path.2).length ≤ _
  rw [List.length_append, selectedInitial_eventCount E problem path.1]
  have tailBound := sampledRecoveryTail_eventCount_original_le
    round (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _
    (samplingRoundEventBound E problem)
    (selectedSamplingRound_eventCount_le E fieldTail sameWidth fits odd problem points seed)
    count path.2
  exact (Nat.add_le_add_left tailBound _).trans_eq (Nat.add_assoc _ _ _).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
