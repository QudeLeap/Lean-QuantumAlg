/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Resources

/-!
# Zero quantum-gate multiplicities of the native classical recovery stages

The sampler, full lattice/quadratic recovery and final optional selector keep
their original classical instruction allowances. Their explicit native lists,
branch maxima and repetitions contain no quantum gate event. The candidate
scan is handled by induction over its original offset list, without replacing
any classical cost by a gate count or enumerating the fixed search window.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.RecoveryNativeGates

noncomputable section

open Execution ClassicalRoutines ShortDLP.CompiledMAU

section Generic

variable {model : ExecutionModel} [BitWord.Selected model]
  (coordinate : model.GateCoordinate)

private lemma constant_gate_zero (width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (ConstantWord.envelope model width) = 0 := by
  simp [ConstantWord.envelope, ConstantWord.bitEnvelope,
    ConstantWord.shiftEvent, ConstantWord.incrementEvent]

private lemma decode_gate_zero (width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (TerminalDecode.envelope (model := model) width) = 0 := by
  simp [TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    TerminalDecode.shiftEvent, TerminalDecode.incrementEvent]

private lemma firstAccepted_gate_zero (width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (FirstAccepted.nativeEnvelope model width) = 0 := by
  simp [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents]

private lemma sampler_gate_zero (N : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
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
    NumberTheory.GCD.remainderEvents, constant_gate_zero, decode_gate_zero,
    firstAccepted_gate_zero]

private lemma power_gate_zero (width exponentWidth : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (Modular.NativePower.eventEnvelope model width exponentWidth) = 0 := by
  simp [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope, constant_gate_zero]

private lemma setup_gate_zero (width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticeCandidateModularSetup.setupEventEnvelope model width) = 0 := by
  simp [LatticeCandidateModularSetup.setupEventEnvelope,
    LatticeCandidateModularSetup.prepareEnvelope, power_gate_zero, constant_gate_zero]

private lemma decoder_gate_zero (N : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (BatchMachine.eventEnvelope (model := model) N) = 0 := by
  simp [BatchMachine.eventEnvelope, BatchMachine.copySplitTrace,
    Word.Split.splitTrace, Word.Split.shiftTrace, decode_gate_zero, List.count_replicate]

private lemma basis_gate_zero (N m ell width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticeBasis.basisEventEnvelope (model := model) N m ell width) = 0 := by
  simp [LatticeBasis.basisEventEnvelope, LatticeBasis.basisTrace,
    LatticeLoading.firstRowTrace, LatticeBasis.powerRowsTrace,
    Word.PowerOfTwo.powerTrace, Word.PowerOfTwo.shiftTrace, List.count_replicate]

private lemma target_gate_zero (m ell width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticeWideTargetMachine.eventEnvelope (model := model) m ell width) = 0 := by
  simp [LatticeWideTargetMachine.eventEnvelope, LatticeWideTargetMachine.preimagesTrace,
    Word.PowerOfTwo.Scale.scaleTrace, Word.PowerOfTwo.shiftTrace,
    LatticeTargetPoint.eventEnvelope, LatticeTarget.eventEnvelope,
    LatticeTarget.prepareTrace, LatticeTarget.arithmeticTrace, List.count_replicate]

private lemma initialized_gate_zero (fuel width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticeWideLllMachine.initializedEventEnvelope (model := model) fuel width) = 0 := by
  rw [LatticeWideLllMachine.initializedEventEnvelope_eq]
  simp [LatticeFixedFuelMachine.refreshResetTrace, LatticeMetricMachine.gramTrace,
    LatticeFixedFuelMachine.resetFirstTrace, LatticeFixedFuelMachine.fixedFuelEventEnvelope,
    NumberTheory.SignedWord.nativeAlphabet]

private lemma nearest_gate_zero (N : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticePairNearestPlaneSavedTarget.eventEnvelope (model := model) N) = 0 := by
  simp [LatticePairNearestPlaneSavedTarget.eventEnvelope,
    LatticeWideLllMachine.eventEnvelope, LatticeWideLllMachine.decodeTargetEventEnvelope,
    LatticeWideInitializationPrefix.eventEnvelope, decoder_gate_zero, basis_gate_zero,
    target_gate_zero, initialized_gate_zero, LatticeRows.pointCopyTrace,
    LatticeNearestPlaneThree.eventEnvelope, NumberTheory.SignedWord.nativeAlphabet]

private lemma slot_gate_zero (coordinateWidth modulusWidth : Nat)
    (offset : NumberTheory.IntegerPoint3) :
    ResourcePool.count (model := model) (.gate coordinate)
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
    LatticeCandidatePowerMachine.candidatePowerEventEnvelope, power_gate_zero,
    LatticeCandidateSelector.candidateSelectorEventEnvelope,
    LatticeCandidateSelector.eligibilityTrace, FirstAccepted.Direct.copyTrace,
    List.count_replicate]

private lemma offsets_gate_zero (coordinateWidth modulusWidth : Nat)
    (offsets : List NumberTheory.IntegerPoint3) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticeCandidateScan.offsetsEventEnvelope model coordinateWidth modulusWidth offsets) =
        0 := by
  induction offsets with
  | nil => rfl
  | cons offset rest ih =>
      rw [LatticeCandidateScan.offsetsEventEnvelope, ResourcePool.count_add,
        slot_gate_zero, ih, Nat.zero_add]

private lemma candidate_gate_zero (N : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticePairCandidateRecovery.recoveryEventEnvelope (model := model) N) = 0 := by
  simp [LatticePairCandidateRecovery.recoveryEventEnvelope,
    LatticePairCandidateRecovery.prefixEventEnvelope,
    LatticePairCandidateRecovery.sharedEventEnvelope, nearest_gate_zero,
    LatticeCandidateConstants.loadTrace, Word.PowerOfTwo.powerTrace,
    Word.PowerOfTwo.shiftTrace, setup_gate_zero,
    LatticeCandidateScanInitialized.initializedScanEventEnvelope,
    LatticeCandidateSelectorInit.clearAcceptedEventEnvelope,
    LatticeCandidateScan.scanEventEnvelope, offsets_gate_zero, List.count_replicate]

private lemma quadratic_gate_zero (width : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
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
    firstAccepted_gate_zero]

private lemma recovery_gate_zero (N : Nat) (additionalMembers : Nat := 14) :
    ResourcePool.count (model := model) (.gate coordinate)
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model) N additionalMembers) = 0
        := by
  simp [LatticeFixedBatchRecoveryMachine.eventEnvelope,
    LatticeBatchRecoveryWorkspaceBody.eventEnvelope,
    LatticeSharedQuadraticInitialization.eventEnvelope, setup_gate_zero,
    QuadraticScratchInitialization.eventEnvelope, QuadraticScratchInitialization.events,
    LatticeBatchRecoveryEndpoint.eventEnvelope, LatticeBatchRecoveryTail.eventEnvelope,
    LatticeEarlyFactorSeed.eventEnvelope, firstAccepted_gate_zero,
    LatticePairRecoveryFold.eventEnvelope, LatticePairReusableRecovery.eventEnvelope,
    LatticePairRecoveryReset.resetEventEnvelope, LatticePairRecoveryReset.nativeTrace,
    LatticePairRecoveryReset.cells, LatticePairRecoveryReset.cellEvent,
    LatticePairFactorRecovery.eventEnvelope, candidate_gate_zero, quadratic_gate_zero,
    LatticeBatchRecoveryOutput.eventEnvelope, LatticeBatchRecoveryOutput.events]

private lemma optional_gate_zero (width count : Nat) :
    ResourcePool.count (model := model) (.gate coordinate)
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope model width count) = 0 := by
  simp [FirstAccepted.Direct.Optional.Allocation.eventEnvelope,
    FirstAccepted.Direct.Optional.eventEnvelope, FirstAccepted.Direct.copyTrace]

end Generic

/-- The actual random draw, residue scan and GCD decision have zero native quantum-gate count. -/
lemma sampler_gate_count_zero (N : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope RuntimeRound.model N) = 0 :=
  sampler_gate_zero (model := RuntimeRound.model) coordinate N

/-- Every native recovery allowance is classical, including both branch arms and all 120 pairs. -/
lemma recovery_gate_count_zero (N : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := RuntimeRound.model) N) = 0 :=
  recovery_gate_zero (model := RuntimeRound.model) coordinate N

/-- Every optional unpack, selected copy and final pack has zero native quantum-gate count. -/
lemma selection_gate_count_zero (N count : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
      (NativeRetrySelection.selectionEnvelope N count) = 0 :=
  optional_gate_zero (model := RuntimeRound.model) coordinate (modulusBits N) count

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.RecoveryNativeGates
