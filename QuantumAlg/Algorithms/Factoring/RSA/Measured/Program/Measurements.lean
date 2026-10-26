/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Resources

/-!
# No physical measurements in the actual classical source and recovery allowance

The unchanged explicit native classical lists, branch maxima and repetitions
contain no physical Z measurement. The original offset scan is handled by
finite induction; its classical work remains separately charged
[EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program.Measurements

noncomputable section

open Execution ClassicalRoutines
open QuantumAlg.Factoring.EkeraHastadStyle.Canonical

variable {model : ExecutionModel} [BitWord.Selected model]
  (dimension : model.SystemDimension)

private lemma constant_measurement_zero (width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (ConstantWord.envelope model width) = 0 := by
  simp [ConstantWord.envelope, ConstantWord.bitEnvelope,
    ConstantWord.shiftEvent, ConstantWord.incrementEvent]

private lemma decode_measurement_zero (width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (TerminalDecode.envelope (model := model) width) = 0 := by
  simp [TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    TerminalDecode.shiftEvent, TerminalDecode.incrementEvent]

private lemma firstAccepted_measurement_zero (width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (FirstAccepted.nativeEnvelope model width) = 0 := by
  simp [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents]

lemma rsaMeasuredClassical_sampler_measurement_zero (N : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope model N) = 0 := by
  simp [ShorStyle.Canonical.Sampler.Retained.nativeEnvelope,
    ShorStyle.Canonical.Sampler.Program.nativeEnvelope,
    ShorStyle.Canonical.Sampler.Proposal.scanEnvelope,
    ShorStyle.Canonical.Sampler.Proposal.slotEnvelope,
    ShorStyle.Canonical.Sampler.Proposal.prefixEnvelope,
    ShorStyle.Canonical.Sampler.Proposal.comparisonEvents,
    ShorStyle.Canonical.Sampler.Decision.nativeEnvelope,
    ShorStyle.Canonical.Sampler.Decision.initializationEvents,
    ShorStyle.Canonical.Sampler.Decision.acceptedEnvelope,
    ShorStyle.Canonical.Sampler.Decision.comparisonEvents,
    ShorStyle.Canonical.Sampler.Decision.resultEnvelope,
    ShorStyle.Canonical.Sampler.Decision.unitEvents,
    ShorStyle.Canonical.Sampler.Decision.factorEvents,
    NumberTheory.GCD.nativeEnvelope, NumberTheory.GCD.initializationEvents,
    NumberTheory.GCD.remainderEvents, constant_measurement_zero, decode_measurement_zero,
    firstAccepted_measurement_zero]

private lemma power_measurement_zero (width exponentWidth : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (Modular.NativePower.eventEnvelope model width exponentWidth) = 0 := by
  simp [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    constant_measurement_zero]

private lemma setup_measurement_zero (width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeCandidateModularSetup.setupEventEnvelope model width) = 0 := by
  simp [LatticeCandidateModularSetup.setupEventEnvelope,
    LatticeCandidateModularSetup.prepareEnvelope, power_measurement_zero, constant_measurement_zero]

private lemma decoder_measurement_zero (N : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (BatchMachine.eventEnvelope (model := model) N) = 0 := by
  simp [BatchMachine.eventEnvelope, BatchMachine.copySplitTrace,
    Word.Split.splitTrace, Word.Split.shiftTrace, decode_measurement_zero, List.count_replicate]

private lemma basis_measurement_zero (N m ell width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeBasis.basisEventEnvelope (model := model) N m ell width) = 0 := by
  simp [LatticeBasis.basisEventEnvelope, LatticeBasis.basisTrace,
    LatticeLoading.firstRowTrace, LatticeBasis.powerRowsTrace,
    Word.PowerOfTwo.powerTrace, Word.PowerOfTwo.shiftTrace, List.count_replicate]

private lemma target_measurement_zero (m ell width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeWideTargetMachine.eventEnvelope (model := model) m ell width) = 0 := by
  simp [LatticeWideTargetMachine.eventEnvelope, LatticeWideTargetMachine.preimagesTrace,
    Word.PowerOfTwo.Scale.scaleTrace, Word.PowerOfTwo.shiftTrace,
    LatticeTargetPoint.eventEnvelope, LatticeTarget.eventEnvelope,
    LatticeTarget.prepareTrace, LatticeTarget.arithmeticTrace, List.count_replicate]

private lemma initialized_measurement_zero (fuel width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeWideLllMachine.initializedEventEnvelope (model := model) fuel width) = 0 := by
  rw [LatticeWideLllMachine.initializedEventEnvelope_eq]
  simp [LatticeFixedFuelMachine.refreshResetTrace, LatticeMetricMachine.gramTrace,
    LatticeFixedFuelMachine.resetFirstTrace, LatticeFixedFuelMachine.fixedFuelEventEnvelope,
    NumberTheory.SignedWord.nativeAlphabet]

private lemma nearest_measurement_zero (N : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticePairNearestPlaneSavedTarget.eventEnvelope (model := model) N) = 0 := by
  simp [LatticePairNearestPlaneSavedTarget.eventEnvelope,
    LatticeWideLllMachine.eventEnvelope, LatticeWideLllMachine.decodeTargetEventEnvelope,
    LatticeWideInitializationPrefix.eventEnvelope, decoder_measurement_zero, basis_measurement_zero,
    target_measurement_zero, initialized_measurement_zero, LatticeRows.pointCopyTrace,
    LatticeNearestPlaneThree.eventEnvelope, NumberTheory.SignedWord.nativeAlphabet]

private lemma slot_measurement_zero (coordinateWidth modulusWidth : Nat)
    (offset : NumberTheory.IntegerPoint3) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeCandidateSlotMachine.candidateSlotEventEnvelope model coordinateWidth
        modulusWidth offset) = 0 := by
  simp [LatticeCandidateSlotMachine.candidateSlotEventEnvelope,
    LatticeCandidateDistancePrefix.prefixTrace, LatticeOffsetMaterializer.offsetTrace,
    ConstantWord.Signed.nativeTrace, ConstantWord.Signed.loopTrace,
    LatticeCandidatePointMachine.candidateTrace, LatticeCandidatePointMachine.coordinateTrace,
    LatticePointDifferenceMachine.differenceTrace, LatticeSquaredDistanceMachine.distanceTrace,
    LatticeNearTargetScale.scaleTrace, LatticeNearTargetScale.copyScaleTrace,
    LatticeCandidateSlotMachine.exponentEnvelope, LatticeCandidateExponent.exponentTrace,
    LatticeCandidateExponent.suffixTrace, NumberTheory.SignedWord.signTrace,
    NumberTheory.SignedWord.magnitudeTrace,
    LatticeCandidatePowerMachine.candidatePowerEventEnvelope, power_measurement_zero,
    LatticeCandidateSelector.candidateSelectorEventEnvelope,
    LatticeCandidateSelector.eligibilityTrace, FirstAccepted.Direct.copyTrace,
    List.count_replicate]

private lemma offsets_measurement_zero (coordinateWidth modulusWidth : Nat)
    (offsets : List NumberTheory.IntegerPoint3) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeCandidateScan.offsetsEventEnvelope model coordinateWidth modulusWidth offsets) =
        0 := by
  induction offsets with
  | nil => rfl
  | cons offset rest ih =>
      rw [LatticeCandidateScan.offsetsEventEnvelope, ResourcePool.count_add,
        slot_measurement_zero, ih, Nat.zero_add]

private lemma candidate_measurement_zero (N : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticePairCandidateRecovery.recoveryEventEnvelope (model := model) N) = 0 := by
  simp [LatticePairCandidateRecovery.recoveryEventEnvelope,
    LatticePairCandidateRecovery.prefixEventEnvelope,
    LatticePairCandidateRecovery.sharedEventEnvelope, nearest_measurement_zero,
    LatticeCandidateConstants.loadTrace, Word.PowerOfTwo.powerTrace,
    Word.PowerOfTwo.shiftTrace, setup_measurement_zero,
    LatticeCandidateScanInitialized.initializedScanEventEnvelope,
    LatticeCandidateSelectorInit.clearAcceptedEventEnvelope,
    LatticeCandidateScan.scanEventEnvelope, offsets_measurement_zero, List.count_replicate]

private lemma quadratic_measurement_zero (width : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (QuadraticRecoveryGuarded.eventEnvelope (model := model) width) = 0 := by
  simp [QuadraticRecoveryGuarded.eventEnvelope,
    QuadraticRecoveryReset.resetEventEnvelope, QuadraticRecoveryReset.nativeTrace,
    QuadraticRecoveryMachine.eventEnvelope, QuadraticCandidates.eventEnvelope,
    QuadraticPrefix.eventEnvelope, QuadraticPrefix.discriminantEnvelope,
    QuadraticPrefix.prepareTrace, NumberTheory.NatSub.eventEnvelope,
    NumberTheory.NatSqrt.eventEnvelope, NumberTheory.NatSqrt.initializationEventEnvelope,
    NumberTheory.IntegerSqrt.roundTrace, QuadraticCandidates.suffixEnvelope,
    QuadraticCandidates.resizeTrace, QuadraticCandidatePairSelect.eventEnvelope,
    QuadraticCandidateSelect.eventEnvelope, QuadraticCandidateCheck.eventEnvelope,
    QuadraticCandidateCheck.positiveEventEnvelope, NumberTheory.NatModCheck.eventEnvelope,
    firstAccepted_measurement_zero]

lemma rsaMeasuredClassical_recovery_measurement_zero (N : Nat) (additionalMembers : Nat := 14) :
    ResourcePool.count (model := model) (.measurement dimension)
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model) N additionalMembers) = 0
        := by
  simp [LatticeFixedBatchRecoveryMachine.eventEnvelope,
    LatticeBatchRecoveryWorkspaceBody.eventEnvelope,
    LatticeSharedQuadraticInitialization.eventEnvelope, setup_measurement_zero,
    QuadraticScratchInitialization.eventEnvelope, QuadraticScratchInitialization.events,
    LatticeBatchRecoveryEndpoint.eventEnvelope, LatticeBatchRecoveryTail.eventEnvelope,
    LatticeEarlyFactorSeed.eventEnvelope, firstAccepted_measurement_zero,
    LatticePairRecoveryFold.eventEnvelope, LatticePairReusableRecovery.eventEnvelope,
    LatticePairRecoveryReset.resetEventEnvelope, LatticePairRecoveryReset.nativeTrace,
    LatticePairRecoveryReset.cells, LatticePairRecoveryReset.cellEvent,
    LatticePairFactorRecovery.eventEnvelope, candidate_measurement_zero, quadratic_measurement_zero,
    LatticeBatchRecoveryOutput.eventEnvelope, LatticeBatchRecoveryOutput.events]

lemma rsaMeasuredClassical_optional_measurement_zero (width count : Nat) :
    ResourcePool.count (model := model) (.measurement dimension)
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope model width count) = 0 := by
  simp [FirstAccepted.Direct.Optional.Allocation.eventEnvelope,
    FirstAccepted.Direct.Optional.eventEnvelope, FirstAccepted.Direct.copyTrace]

end

end QuantumAlg.Factoring.RSA.Measured.Program.Measurements
