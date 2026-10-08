/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Selection
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.NativePool
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Native event budgets for actual completed ECC sections

The source reset and complete sampled recovery are bounded on each original
interpreter path. The first nonterminal section charges its own sample plus
the following physical reset, using the independent checked-section budget.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] underPersistent persistentCtx

private theorem pool_le_of_trace_equiv {model : ExecutionModel}
    {base outer : RuntimeCtx model.kind}
    (code : Circuit model base base) (framed : Circuit model outer outer)
    (paths : code.Path ≃ framed.Path)
    (same : ∀ path, framed.eventTrace (paths path) = code.eventTrace path)
    (budget : ResourcePool model)
    (bounded : ∀ path, code.resourcePool path ≤ budget)
    (path : framed.Path) : framed.resourcePool path ≤ budget := by
  have equalPool : framed.resourcePool path = code.resourcePool (paths.symm path) := by
    have traceEq := same (paths.symm path)
    simpa only [Circuit.resourcePool, Equiv.apply_symm_apply] using
      congrArg ResourcePool.ofList traceEq
  exact equalPool.le.trans (bounded (paths.symm path))

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private theorem selectedReset_pool_le
    (path : (BitWord.selectForCircuit
      (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)).Path) :
    (BitWord.selectForCircuit
      (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)).resourcePool path ≤
      BitWord.liftQuantumPool (samplingResetBudget E (orderWidth problem)) := by
  let source := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  calc
    (BitWord.selectForCircuit source).resourcePool path =
        BitWord.liftQuantumPool (source.resourcePool original) := by
      simpa only [aligned] using BitWord.selectForCircuit_resourcePool source original
    _ ≤ BitWord.liftQuantumPool (samplingResetBudget E (orderWidth problem)) :=
      Multiset.map_le_map
        (samplingReset_pool_le E fieldTail (orderWidth problem) sameWidth fits seed original)

private theorem selectedReadout_pool_le
    (path : (BitWord.selectForCircuit
      (samplingReadout E fieldTail odd problem points)).Path) :
    (BitWord.selectForCircuit
      (samplingReadout E fieldTail odd problem points)).resourcePool path ≤
      BitWord.liftQuantumPool (samplingRoundBudget E problem) := by
  let source := samplingReadout E fieldTail odd problem points
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  have sourceBound : source.resourcePool original ≤ samplingRoundBudget E problem := by
    have readoutBound := samplingReadout_budget E fieldTail odd problem points original
    exact readoutBound.trans (by
      unfold samplingRoundBudget
      exact Multiset.le_add_left _ _)
  calc
    (BitWord.selectForCircuit source).resourcePool path =
        BitWord.liftQuantumPool (source.resourcePool original) := by
      simpa only [aligned] using BitWord.selectForCircuit_resourcePool source original
    _ ≤ BitWord.liftQuantumPool (samplingRoundBudget E problem) :=
      Multiset.map_le_map sourceBound

/-- The unchanged complete reset/sample/check attempt charges every selected
quantum event and each original native classical recovery event. -/
theorem persistentCheckedAttempt_pool_le
    (path : (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
      nontrivial).resourcePool path ≤
      BitWord.liftQuantumPool (samplingRoundBudget E problem) +
        attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
          (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  exact sampledAttempt_pool_le
    (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed))
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))
    (BitWord.liftQuantumPool (samplingRoundBudget E problem))
    (selectedSamplingRound_pool_le E fieldTail sameWidth fits odd problem points seed) path

/-- Every actual path of the first reset/sample/check/next-reset section fits
the independently declared complete-section event budget. -/
theorem firstCheckedSection_pool_le
    (path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).resourcePool path ≤
      checkedSectionEventBudget E problem nontrivial := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let attempt := persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
    nontrivial
  let equivalent : Circuit.OperationalEquiv
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)
      (attempt.seq reset) :=
    (persistentCheckedAttempt_operationalEquiv E fieldTail sameWidth fits odd problem
      points seed nontrivial).append reset |>.symm
  let original := equivalent.path path
  have poolEq :
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).resourcePool path =
        (attempt.seq reset).resourcePool original :=
    congrArg ResourcePool.ofList (equivalent.events path)
  rw [poolEq]
  change ResourcePool.ofList (attempt.eventTrace original.1 ++ reset.eventTrace original.2)
    ≤ checkedSectionEventBudget E problem nontrivial
  rw [ResourcePool.ofList_append]
  let resetSource := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let selectedReset := BitWord.selectForCircuit resetSource
  have selectedLocal : selectedReset.IsLocal := BitWord.selectForCircuit_isLocal resetSource
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  exact add_le_add
    (persistentCheckedAttempt_pool_le E fieldTail sameWidth fits odd problem points seed
      nontrivial original.1)
    (pool_le_of_trace_equiv selectedReset reset
      (underPersistentPathEquiv selectedReset selectedLocal
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (underPersistent_pathResources selectedReset selectedLocal
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).1
      (BitWord.liftQuantumPool (samplingResetBudget E (orderWidth problem)))
      (selectedReset_pool_le E fieldTail sameWidth fits problem seed) original.2)

/-- Every actual reused readout/check/next-reset path fits the same complete
section allowance. Its initial reset is the preceding section's charged end. -/
theorem reusedCheckedSection_pool_le
    (path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).resourcePool path ≤
      checkedSectionEventBudget E problem nontrivial := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  change ResourcePool.ofList (body.eventTrace path.1 ++ reset.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  let sample := BitWord.selectForCircuit (samplingReadout E fieldTail odd problem points)
  have sampleLocal : sample.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReadout_isLocal E fieldTail odd problem points)
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  have bodyBound : body.resourcePool path.1 ≤
      BitWord.liftQuantumPool (samplingRoundBudget E problem) +
        attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
          (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) := by
    exact sampledAttempt_pool_le sample sampleLocal
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
      (PublicInput.terminalTargetRef E (orderWidth problem))
      (BitWord.liftQuantumPool (samplingRoundBudget E problem))
      (selectedReadout_pool_le E fieldTail odd problem points) path.1
  let resetSource := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let selectedReset := BitWord.selectForCircuit resetSource
  have selectedLocal : selectedReset.IsLocal := BitWord.selectForCircuit_isLocal resetSource
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  exact add_le_add bodyBound
    (pool_le_of_trace_equiv selectedReset reset
      (underPersistentPathEquiv selectedReset selectedLocal
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (underPersistent_pathResources selectedReset selectedLocal
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).1
      (BitWord.liftQuantumPool (samplingResetBudget E (orderWidth problem)))
      (selectedReset_pool_le E fieldTail sameWidth fits problem seed) path.2)

/-- The first actual complete section meets the independent protocol's
unit-duration whole-section depth limit on the same supported path. -/
theorem firstCheckedSection_problemDepth
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
      addends).depth.Holds
        (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial) path := by
  change (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).depth (fun _ => 1) path ≤
    ResourcePool.weightedCount (fun _ => 1)
      (checkedSectionEventBudget E problem nontrivial)
  exact Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path
    (firstCheckedSection_pool_le E fieldTail sameWidth fits odd problem points seed
      nontrivial path)

/-- The reused actual complete section satisfies its seeded-input protocol's
unit-duration depth limit without charging an extra initial reset. -/
theorem reusedCheckedSection_problemDepth
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).Path) :
    (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
      addends).depth.Holds
        (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial) path := by
  change (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).depth (fun _ => 1) path ≤
    ResourcePool.weightedCount (fun _ => 1)
      (checkedSectionEventBudget E problem nontrivial)
  exact Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path
    (reusedCheckedSection_pool_le E fieldTail sameWidth fits odd problem points seed
      nontrivial path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
