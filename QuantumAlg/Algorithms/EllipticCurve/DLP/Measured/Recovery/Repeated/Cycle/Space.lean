/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Resources

/-!
# Live space of complete checked ECC sections

Each actual nonterminal section uses the existing seven-cell bank. The
checked recovery's lexical scratch and the physical reset occur in successive
scopes, so neither section duplicates its live storage.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] underPersistent persistentCtx

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private theorem checkedAttempt_resident_le
    (path : (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).peakResidentSpace path ≤
      recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)).residentSpace := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  exact (sampledAttempt_resident_le
    (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed))
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) path).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)

private theorem checkedAttempt_auxiliary_le
    (path : (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).peakAuxiliarySpace path ≤
      recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)).auxiliarySpace := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  exact (sampledAttempt_auxiliary_le
    (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed))
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem)) path).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)

private theorem lifted_resident_le {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (source : Circuit model ctx ctx)
    (supported : source.IsLocal) (width scalarWidth : Nat)
    (scratch : SpacePool model.kind)
    (path : (underPersistent source supported width scalarWidth).Path) :
    (underPersistent source supported width scalarWidth).peakResidentSpace path ≤
      scratch + (persistentCtx ctx width scalarWidth).residentSpace := by
  exact ((underPersistent_space source supported width scalarWidth).1 path).le.trans
    (fun _ => Nat.le_add_left _ _)

private theorem lifted_auxiliary_le {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (source : Circuit model ctx ctx)
    (supported : source.IsLocal) (width scalarWidth : Nat)
    (scratch : SpacePool model.kind)
    (path : (underPersistent source supported width scalarWidth).Path) :
    (underPersistent source supported width scalarWidth).peakAuxiliarySpace path ≤
      scratch + (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  exact ((underPersistent_space source supported width scalarWidth).2 path).le.trans
    (fun _ => Nat.le_add_left _ _)

/-- The first real reset/sample/check/reset section fits the independent
resident allowance on every interpreter path. -/
theorem firstCheckedSection_resident_le
    (path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).peakResidentSpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).resident := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let attempt := persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
    nontrivial
  let source := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  have supported : source.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  let equivalent : Circuit.OperationalEquiv
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)
      (attempt.seq reset) :=
    (persistentCheckedAttempt_operationalEquiv E fieldTail sameWidth fits odd problem
      points seed nontrivial).append reset |>.symm
  have equivalentSpace := equivalent.resident path
  rw [equivalentSpace]
  refine (Circuit.peakResidentSpace_seq attempt reset (equivalent.path path)).le.trans
    (SpacePool.max_le ?_ ?_)
  · exact (checkedAttempt_resident_le E fieldTail sameWidth fits odd problem points seed
      nontrivial (equivalent.path path).1).trans (by
        simp only [checkedSectionResourceBudget, persistentCtx_residentSpace, add_assoc]
        exact le_rfl)
  · exact (lifted_resident_le source supported (Canonical.Layout.fieldWidth E)
      (orderWidth problem) (recoveryTailScratchSpace .quantum
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (equivalent.path path).2).trans (by
        simp only [checkedSectionResourceBudget, persistentCtx_residentSpace, add_assoc]
        exact le_rfl)

/-- The first section's auxiliary peak includes one reused checked scratch
scope and one persistent bank. -/
theorem firstCheckedSection_auxiliary_le
    (path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).peakAuxiliarySpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).auxiliary := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let attempt := persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
    nontrivial
  let source := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  have supported : source.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  let equivalent : Circuit.OperationalEquiv
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)
      (attempt.seq reset) :=
    (persistentCheckedAttempt_operationalEquiv E fieldTail sameWidth fits odd problem
      points seed nontrivial).append reset |>.symm
  have equivalentSpace := equivalent.auxiliary path
  rw [equivalentSpace]
  refine (Circuit.peakAuxiliarySpace_seq attempt reset (equivalent.path path)).le.trans
    (SpacePool.max_le ?_ ?_)
  · exact (checkedAttempt_auxiliary_le E fieldTail sameWidth fits odd problem points seed
      nontrivial (equivalent.path path).1).trans (by
        simp only [checkedSectionResourceBudget, persistentCtx_auxiliarySpace, add_assoc]
        exact le_rfl)
  · exact (lifted_auxiliary_le source supported (Canonical.Layout.fieldWidth E)
      (orderWidth problem) (recoveryTailScratchSpace .quantum
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (equivalent.path path).2).trans (by
        simp only [checkedSectionResourceBudget, persistentCtx_auxiliarySpace, add_assoc]
        exact le_rfl)

/-- The reused readout/check/reset section has the same resident envelope,
without charging a second initial reset. -/
theorem reusedCheckedSection_resident_le
    (path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).peakResidentSpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).resident := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  let source := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  have supported : source.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  refine (Circuit.peakResidentSpace_seq body reset path).le.trans
    (SpacePool.max_le ?_ ?_)
  · let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
    have bounded := sampledAttempt_resident_le
      (BitWord.selectForCircuit (samplingReadout E fieldTail odd problem points))
      (BitWord.selectForCircuit_isLocal _
        (samplingReadout_isLocal E fieldTail odd problem points))
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (rawRecoveryInput problem measured)
      (PublicInput.terminalBaseRef E (orderWidth problem))
      (PublicInput.terminalTargetRef E (orderWidth problem)) path.1
    exact bounded.trans ((add_le_add (SpacePool.le_max_left _ _) le_rfl).trans (by
      simp only [checkedSectionResourceBudget, persistentCtx_residentSpace, add_assoc]
      exact le_rfl))
  · exact (lifted_resident_le source supported (Canonical.Layout.fieldWidth E)
      (orderWidth problem) (recoveryTailScratchSpace .quantum
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) path.2).trans (by
      simp only [checkedSectionResourceBudget, persistentCtx_residentSpace, add_assoc]
      exact le_rfl)

/-- The reused section also reuses its auxiliary scratch scope. -/
theorem reusedCheckedSection_auxiliary_le
    (path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).peakAuxiliarySpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).auxiliary := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  let source := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  have supported : source.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  refine (Circuit.peakAuxiliarySpace_seq body reset path).le.trans
    (SpacePool.max_le ?_ ?_)
  · let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
    have bounded := sampledAttempt_auxiliary_le
      (BitWord.selectForCircuit (samplingReadout E fieldTail odd problem points))
      (BitWord.selectForCircuit_isLocal _
        (samplingReadout_isLocal E fieldTail odd problem points))
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (rawRecoveryInput problem measured)
      (PublicInput.terminalBaseRef E (orderWidth problem))
      (PublicInput.terminalTargetRef E (orderWidth problem)) path.1
    exact bounded.trans ((add_le_add (SpacePool.le_max_left _ _) le_rfl).trans (by
      simp only [checkedSectionResourceBudget, persistentCtx_auxiliarySpace, add_assoc]
      exact le_rfl))
  · exact (lifted_auxiliary_le source supported (Canonical.Layout.fieldWidth E)
      (orderWidth problem) (recoveryTailScratchSpace .quantum
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) path.2).trans (by
      simp only [checkedSectionResourceBudget, persistentCtx_auxiliarySpace, add_assoc]
      exact le_rfl)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
