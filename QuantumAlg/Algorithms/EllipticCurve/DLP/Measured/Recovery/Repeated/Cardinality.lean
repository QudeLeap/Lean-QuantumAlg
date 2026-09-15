/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.RoundResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Cardinality

/-!
# Actual repeated-sampling and original classical event ceiling

True reset traces contain three events per original physical wire. Each round
then incurs the original quantum sampling/readout allowance and the original
complete classical recovery ceiling. The two original preparations and one
final option pack occur once. All iteration counts, including zero, describe
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

/-- Actual reset count plus the original finite native sampling and readout allowance. -/
def samplingRoundEventBound : Nat :=
  3 * (PublicInput.terminal E (orderWidth problem)).systemCount +
    ((exponentPreparationCircuit problem).eventCost +
      (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale (2 * orderWidth problem) (MeasuredPointAddition.events p.size)) +
      (exponentReadoutCircuit problem).eventCost +
      (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2)).card

/-- The actual reset contributes exactly three per wire, independently of its branch pool. -/
theorem samplingRound_eventCount_le
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    ((samplingRound E fieldTail sameWidth fits odd problem points seed).eventTrace path).length ≤
      samplingRoundEventBound E problem := by
  change List.length
    ((samplingReset E fieldTail (orderWidth problem) sameWidth fits seed).eventTrace path.1 ++
      (samplingReadout E fieldTail odd problem points).eventTrace path.2) ≤ _
  rw [List.length_append, samplingReset_eventCount]
  exact Nat.add_le_add_left
    (Multiset.card_le_card (samplingReadout_budget E fieldTail odd problem points path.2)) _

/-- Each round retains the original complete classical recovery ceiling in its event count. -/
theorem exponentRepeatedRun_eventCount_le (nontrivial : 2 ≤ problem.order) (count : Nat)
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    ((exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.eventTrace path).length ≤
        2 + count * (samplingRoundEventBound E problem +
          (42 * orderWidth problem +
            orderWidth problem * (248 * Canonical.Layout.fieldWidth E + 644) + 119)) + 1 := by
  change
    (((PublicInput.initializeWork E (orderWidth problem)).eventTrace path.1.1 ++
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace path.1.2) ++ _).length ≤ _
  have noEvents :
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace path.1.2 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [noEvents, List.append_nil, List.length_append, PublicInput.initializeWork_eventTrace]
  have tailBound := sampledRecoveryTail_eventCount_original_le
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _
    (samplingRoundEventBound E problem)
    (samplingRound_eventCount_le E fieldTail sameWidth fits odd problem points seed) count path.2
  exact (Nat.add_le_add_left tailBound 2).trans_eq (Nat.add_assoc _ _ _).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
