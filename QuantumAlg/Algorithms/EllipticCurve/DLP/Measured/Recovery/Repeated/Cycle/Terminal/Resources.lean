/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Terminal.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Terminal.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Space
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# Native resources and borrowed restoration of the terminal ECC body

The last `S;C` path has no next reset. Its independent event budget charges
only its actual readout and checked recovery; the already allocated bank and
scratch bound its resident and auxiliary peaks.
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

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The final actual readout/check charges no following reset. -/
theorem terminalCheckedSection_pool_le
    (path : (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).Path) :
    (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).resourcePool
      path ≤ terminalCheckedSectionEventBudget E problem nontrivial := by
  let sample := BitWord.selectForCircuit (samplingReadout E fieldTail odd problem points)
  have sampleLocal : sample.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReadout_isLocal E fieldTail odd problem points)
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  exact sampledAttempt_pool_le sample sampleLocal
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))
    (BitWord.liftQuantumPool (samplingRoundBudget E problem))
    (selectedReadout_pool_le E fieldTail odd problem points) path

/-- The unchanged final body reuses one recovery scratch scope and bank. -/
theorem terminalCheckedSection_resident_le
    (path : (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).Path) :
    (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).peakResidentSpace
      path ≤ (terminalCheckedSectionResourceBudget E problem nontrivial).resident := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  have bounded := sampledAttempt_resident_le
    (BitWord.selectForCircuit (samplingReadout E fieldTail odd problem points))
    (BitWord.selectForCircuit_isLocal _
      (samplingReadout_isLocal E fieldTail odd problem points))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured)
    (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) path
  exact bounded.trans ((add_le_add (SpacePool.le_max_left _ _) le_rfl).trans (by
    simp only [terminalCheckedSectionResourceBudget, checkedSectionResourceBudget,
      persistentCtx_residentSpace, add_assoc]
    exact le_rfl))

/-- The final body likewise reuses the same auxiliary scratch scope. -/
theorem terminalCheckedSection_auxiliary_le
    (path : (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).Path) :
    (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).peakAuxiliarySpace
      path ≤ (terminalCheckedSectionResourceBudget E problem nontrivial).auxiliary := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  have bounded := sampledAttempt_auxiliary_le
    (BitWord.selectForCircuit (samplingReadout E fieldTail odd problem points))
    (BitWord.selectForCircuit_isLocal _
      (samplingReadout_isLocal E fieldTail odd problem points))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured)
    (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) path
  exact bounded.trans ((add_le_add (SpacePool.le_max_left _ _) le_rfl).trans (by
    simp only [terminalCheckedSectionResourceBudget, checkedSectionResourceBudget,
      persistentCtx_auxiliarySpace, add_assoc]
    exact le_rfl))

/-- Unit-weighted whole-section depth follows from the same actual path's
native event budget, without claiming a following reset. -/
theorem terminalCheckedSection_problemDepth
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).Path) :
    (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points seed
      nontrivial addends).depth.Holds
        (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) path := by
  change (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).depth
    (fun _ => 1) path ≤ ResourcePool.weightedCount (fun _ => 1)
      (terminalCheckedSectionEventBudget E problem nontrivial)
  exact Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path
    (terminalCheckedSection_pool_le E fieldTail odd problem points nontrivial path)

/-- The final body preserves every borrowed and external-reference observation,
despite leaving its owned quantum output unrestricted. -/
theorem terminalCheckedSection_problemBorrowed
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference) :
    (terminalCheckedSectionRun E fieldTail odd problem points nontrivial).RestoresBorrowed
      input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
    (terminalCheckedSectionRun E fieldTail odd problem points nontrivial) ?_ input
  intro Reference H _ state
  have noQuantum : (sectionCtx E problem).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (terminalCheckedSectionCode E fieldTail odd problem points nontrivial)
    noQuantum Reference state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
