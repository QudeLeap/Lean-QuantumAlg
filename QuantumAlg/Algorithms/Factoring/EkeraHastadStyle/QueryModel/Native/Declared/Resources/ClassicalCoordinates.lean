/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources

/-!
# Classical coordinates of the original sampler and batch recovery allowances

The unchanged native allowances contain only classical-operation labels.
The candidate-offset scan is handled for an arbitrary list, so this proof
never enumerates the original large offset family. Branch maxima, fixed-fuel
bounds and every actual arithmetic stage remain in the original allowances.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] (event : Resource.Event model)
    (outside : ∀ label, event ≠ .classicalOperation label)

include outside

/-- The actual sampled-source allowance has no other event coordinate. -/
theorem declared_source_count_eq_zero (N : Nat) :
    ResourcePool.count event (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope model N) =
      0 := by
  simp [Factoring.ShorStyle.Canonical.Sampler.Retained.nativeEnvelope,
    Factoring.ShorStyle.Canonical.Sampler.Program.nativeEnvelope, ConstantWord.envelope,
    ConstantWord.bitEnvelope, Factoring.ShorStyle.Canonical.Sampler.Proposal.scanEnvelope,
    Factoring.ShorStyle.Canonical.Sampler.Proposal.slotEnvelope,
    Factoring.ShorStyle.Canonical.Sampler.Proposal.prefixEnvelope, TerminalDecode.envelope,
    TerminalDecode.bitEnvelope, Factoring.ShorStyle.Canonical.Sampler.Proposal.comparisonEvents,
    FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    Factoring.ShorStyle.Canonical.Sampler.Decision.nativeEnvelope,
    Factoring.ShorStyle.Canonical.Sampler.Decision.initializationEvents,
    Factoring.ShorStyle.Canonical.Sampler.Decision.acceptedEnvelope,
    NumberTheory.GCD.nativeEnvelope, NumberTheory.GCD.initializationEvents,
    NumberTheory.GCD.remainderEvents,
    Factoring.ShorStyle.Canonical.Sampler.Decision.comparisonEvents,
    Factoring.ShorStyle.Canonical.Sampler.Decision.resultEnvelope,
    Factoring.ShorStyle.Canonical.Sampler.Decision.unitEvents,
    Factoring.ShorStyle.Canonical.Sampler.Decision.factorEvents,
    ConstantWord.shiftEvent, ConstantWord.incrementEvent, TerminalDecode.shiftEvent,
    TerminalDecode.incrementEvent, outside, eq_comm]

private theorem slot_zero (coordinateWidth modulusWidth : Nat)
    (offset : QuantumAlg.NumberTheory.IntegerPoint3) :
    ResourcePool.count event
      (LatticeCandidateSlotMachine.candidateSlotEventEnvelope model coordinateWidth modulusWidth
        offset) = 0 := by
  simp [LatticeCandidateSlotMachine.candidateSlotEventEnvelope,
    LatticeCandidateDistancePrefix.prefixTrace, LatticeOffsetMaterializer.offsetTrace,
    ConstantWord.Signed.nativeTrace, ConstantWord.Signed.loopTrace,
    LatticeCandidatePointMachine.candidateTrace, LatticeCandidatePointMachine.coordinateTrace,
    LatticePointDifferenceMachine.differenceTrace, LatticeSquaredDistanceMachine.distanceTrace,
    LatticeNearTargetScale.scaleTrace,
    LatticeNearTargetScale.copyScaleTrace, LatticeCandidateSlotMachine.exponentEnvelope,
    LatticeCandidateExponent.exponentTrace, NumberTheory.SignedWord.signTrace,
    NumberTheory.SignedWord.magnitudeTrace, LatticeCandidateExponent.suffixTrace,
    LatticeCandidatePowerMachine.candidatePowerEventEnvelope, Modular.NativePower.eventEnvelope,
    ConstantWord.envelope, ConstantWord.bitEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    LatticeCandidateSelector.candidateSelectorEventEnvelope,
    LatticeCandidateSelector.eligibilityTrace, FirstAccepted.Direct.copyTrace,
    ResourcePool.ofList_replicate,
    ConstantWord.shiftEvent, ConstantWord.incrementEvent, outside, eq_comm]

private theorem offsets_zero (coordinateWidth modulusWidth : Nat)
    (offsets : List QuantumAlg.NumberTheory.IntegerPoint3) :
    ResourcePool.count event
      (LatticeCandidateScan.offsetsEventEnvelope model coordinateWidth modulusWidth offsets) =
        0 := by
  induction offsets with
  | nil => rfl
  | cons offset tail ih =>
      simp only [LatticeCandidateScan.offsetsEventEnvelope, ResourcePool.count_add,
        slot_zero event outside, ih, add_zero]

/-- Every non-classical-operation coordinate is absent from the original recovery allowance. -/
theorem declared_recovery_count_eq_zero (N : Nat) :
    ResourcePool.count event
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model) N) = 0 := by
  simp [LatticeFixedBatchRecoveryMachine.eventEnvelope,
    LatticeBatchRecoveryWorkspaceBody.eventEnvelope,
    LatticeSharedQuadraticInitialization.eventEnvelope,
    LatticeCandidateModularSetup.setupEventEnvelope, LatticeCandidateModularSetup.prepareEnvelope,
    QuadraticScratchInitialization.eventEnvelope, QuadraticScratchInitialization.events,
    LatticeBatchRecoveryEndpoint.eventEnvelope, LatticeBatchRecoveryTail.eventEnvelope,
    LatticeEarlyFactorSeed.eventEnvelope, FirstAccepted.nativeEnvelope,
    FirstAccepted.decisionEvents, FirstAccepted.copyEvents, LatticePairRecoveryFold.eventEnvelope,
    LatticePairReusableRecovery.eventEnvelope, LatticePairRecoveryReset.resetEventEnvelope,
    LatticePairRecoveryReset.nativeTrace, LatticePairRecoveryReset.cellEvent,
    LatticePairRecoveryReset.cells, LatticePairFactorRecovery.eventEnvelope,
    LatticePairCandidateRecovery.recoveryEventEnvelope,
    LatticePairCandidateRecovery.prefixEventEnvelope,
    LatticePairNearestPlaneSavedTarget.eventEnvelope, LatticeWideLllMachine.eventEnvelope,
    LatticeWideLllMachine.decodeTargetEventEnvelope, LatticeWideInitializationPrefix.eventEnvelope,
    BatchMachine.eventEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    BatchMachine.copySplitTrace, Word.Split.splitTrace, Word.Split.shiftTrace,
    LatticeBasis.basisEventEnvelope, LatticeBasis.basisTrace, LatticeLoading.firstRowTrace,
    Word.PowerOfTwo.powerTrace, Word.PowerOfTwo.shiftTrace, LatticeBasis.powerRowsTrace,
    LatticeWideTargetMachine.eventEnvelope, LatticeWideTargetMachine.preimagesTrace,
    Word.PowerOfTwo.Scale.scaleTrace, LatticeTargetPoint.eventEnvelope,
    LatticeTarget.eventEnvelope, LatticeTarget.prepareTrace, LatticeTarget.arithmeticTrace,
    LatticeFixedFuelMachine.refreshResetTrace, LatticeMetricMachine.gramTrace,
    LatticeFixedFuelMachine.resetFirstTrace, LatticeFixedFuelMachine.fixedFuelEventEnvelope,
    NumberTheory.SignedWord.nativeAlphabet, LatticeRows.pointCopyTrace,
    LatticeNearestPlaneThree.eventEnvelope, LatticePairCandidateRecovery.sharedEventEnvelope,
    LatticeCandidateConstants.loadTrace,
    LatticeCandidateScanInitialized.initializedScanEventEnvelope,
    LatticeCandidateSelectorInit.clearAcceptedEventEnvelope,
    LatticeCandidateScan.scanEventEnvelope, QuadraticRecoveryGuarded.eventEnvelope,
    QuadraticRecoveryReset.resetEventEnvelope, QuadraticRecoveryReset.nativeTrace,
    QuadraticRecoveryMachine.eventEnvelope, QuadraticCandidates.eventEnvelope,
    QuadraticPrefix.eventEnvelope, QuadraticPrefix.discriminantEnvelope,
    QuadraticPrefix.prepareTrace, NumberTheory.NatSub.eventEnvelope,
    NumberTheory.NatSqrt.eventEnvelope, NumberTheory.NatSqrt.initializationEventEnvelope,
    NumberTheory.IntegerSqrt.roundTrace, QuadraticCandidates.suffixEnvelope,
    QuadraticCandidates.resizeTrace, QuadraticCandidatePairSelect.eventEnvelope,
    QuadraticCandidateSelect.eventEnvelope, QuadraticCandidateCheck.eventEnvelope,
    QuadraticCandidateCheck.positiveEventEnvelope, NumberTheory.NatModCheck.eventEnvelope,
    LatticeBatchRecoveryOutput.eventEnvelope, LatticeBatchRecoveryOutput.events,
    LatticeWideLllMachine.initializedEventEnvelope_eq, offsets_zero event outside,
    ResourcePool.ofList_replicate, ConstantWord.envelope, ConstantWord.bitEnvelope,
    ConstantWord.shiftEvent, ConstantWord.incrementEvent, TerminalDecode.shiftEvent,
    TerminalDecode.incrementEvent, Modular.NativePower.eventEnvelope,
    Modular.NativePower.exponentEnvelope, Modular.NativePower.bitEnvelope,
    Modular.NativePower.multiplyEnvelope, outside, eq_comm]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
