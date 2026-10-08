/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Candidate
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Quadratic
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-!
# Closed scalar ceilings for complete native batch recovery

The coordinate allowance includes both branch arms and the full signed-word
alphabet used by LLL and nearest-plane recovery. Its cardinality therefore has
its own ceiling. The actual allocated circuit inherits that ceiling from its
native pool theorem, including initialization, all 120 pairs, thirteen paid
classical clears per pair, and the final output writes.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedBatchRecoveryMachine

open Execution ClassicalRoutines LatticeRecoveryResources

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]

/-- Full signed-word coordinate allowance for source loading, LLL, and nearest plane. -/
def nearestPlaneEnvelopeBound (m ell : Nat) : Nat :=
  8 * m + 12 * ell + 2243 + 2210 * RSA.shortLogRecoveryFuel m ell

/-- Independent width ceiling for the complete native coordinate allowance. -/
def eventCountBound (modulusWidth m ell coordinateWidth : Nat) : Nat :=
  modularSetupCardBound modulusWidth + 11 + 120 *
    (13 + (nearestPlaneEnvelopeBound m ell + (m + 3) +
      modularSetupCardBound modulusWidth + candidateScanCardBound modulusWidth coordinateWidth +
      quadraticGuardedCardBound coordinateWidth))

private theorem decoder_card (N : Nat) :
    (BatchMachine.eventEnvelope (model := model) N).card =
      2 * measurementBits N + tradeoffBits N + 3 := by
  simp [BatchMachine.eventEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    BatchMachine.copySplitTrace, Word.Split.splitTrace, Word.Split.shiftTrace,
    BatchMachine.KWidth,
    ResourcePool.ofList, ResourcePool.scale, ResourcePool.singleton]
  omega

private theorem basis_card (N m ell width : Nat) :
    (LatticeBasis.basisEventEnvelope (model := model) N m ell width).card =
      2 * (ell + m) + 8 := by
  simp [LatticeBasis.basisEventEnvelope, LatticeBasis.basisTrace, LatticeLoading.firstRowTrace,
    LatticeBasis.powerRowsTrace, Word.PowerOfTwo.powerTrace, Word.PowerOfTwo.shiftTrace,
    ResourcePool.ofList]
  omega

private theorem target_card (m ell width : Nat) :
    (LatticeWideTargetMachine.eventEnvelope (model := model) m ell width).card =
      2 * m + 18 := by
  simp [LatticeWideTargetMachine.eventEnvelope, LatticeWideTargetMachine.preimagesTrace,
    Word.PowerOfTwo.Scale.scaleTrace, Word.PowerOfTwo.shiftTrace,
    LatticeTargetPoint.eventEnvelope, LatticeTarget.eventEnvelope, LatticeTarget.prepareTrace,
    LatticeTarget.arithmeticTrace, ResourcePool.ofList]
  omega

private theorem initialized_card (fuel width : Nat) :
    (LatticeWideLllMachine.initializedEventEnvelope (model := model) fuel width).card =
      32 + 2210 * fuel := by
  rw [LatticeWideLllMachine.initializedEventEnvelope_eq]
  simp [LatticeFixedFuelMachine.refreshResetTrace, LatticeMetricMachine.gramTrace,
    LatticeFixedFuelMachine.resetFirstTrace, LatticeFixedFuelMachine.fixedFuelEventEnvelope,
    ClassicalRoutines.NumberTheory.SignedWord.nativeAlphabet, ResourcePool.ofList]
  omega

private theorem nearest_card (N : Nat) :
    (LatticePairNearestPlaneSavedTarget.eventEnvelope (model := model) N).card =
      nearestPlaneEnvelopeBound (shortLogBits N) (tradeoffBits N) := by
  have measurementEq : measurementBits N = shortLogBits N + 2 * tradeoffBits N := by
    unfold measurementBits
    omega
  simp only [LatticePairNearestPlaneSavedTarget.eventEnvelope,
    LatticeWideLllMachine.eventEnvelope, LatticeWideLllMachine.decodeTargetEventEnvelope,
    LatticeWideInitializationPrefix.eventEnvelope, Multiset.card_add, decoder_card,
    basis_card, target_card, initialized_card]
  rw [measurementEq]
  simp [LatticeRows.pointCopyTrace, LatticeNearestPlaneThree.eventEnvelope,
    ClassicalRoutines.NumberTheory.SignedWord.nativeAlphabet, ResourcePool.ofList,
    nearestPlaneEnvelopeBound]
  omega

private theorem candidate_card_le (N : Nat) :
    (LatticePairCandidateRecovery.recoveryEventEnvelope (model := model) N).card ≤
      nearestPlaneEnvelopeBound (shortLogBits N) (tradeoffBits N) + (shortLogBits N + 3) +
        modularSetupCardBound (modulusBits N) +
        candidateScanCardBound (modulusBits N) (LatticePairCandidateRecovery.Width N) := by
  have scan := initializedScanEventEnvelope_card_le (model := model)
    N (shortLogBits N) (tradeoffBits N)
  unfold LatticePairCandidateRecovery.recoveryEventEnvelope
    LatticePairCandidateRecovery.prefixEventEnvelope
    LatticePairCandidateRecovery.sharedEventEnvelope
  rw [Multiset.card_add, Multiset.card_add, Multiset.card_add, nearest_card,
    modularSetupEventEnvelope_card_eq]
  have constants :
      (ResourcePool.ofList (LatticeCandidateConstants.loadTrace (model := model)
        (shortLogBits N) (LatticePairCandidateRecovery.Width N))).card = shortLogBits N + 3 := by
    simp [LatticeCandidateConstants.loadTrace, Word.PowerOfTwo.powerTrace,
      Word.PowerOfTwo.shiftTrace, ResourcePool.ofList]
  rw [constants]
  exact (Nat.add_le_add_left scan _).trans_eq (by simp only [Nat.add_assoc])

private theorem reusable_card_le (N : Nat) :
    (LatticePairReusableRecovery.eventEnvelope (model := model) N).card ≤
      13 + (nearestPlaneEnvelopeBound (shortLogBits N) (tradeoffBits N) +
        (shortLogBits N + 3) + modularSetupCardBound (modulusBits N) +
        candidateScanCardBound (modulusBits N) (LatticePairCandidateRecovery.Width N) +
        quadraticGuardedCardBound (LatticePairCandidateRecovery.Width N)) := by
  have candidate := candidate_card_le (model := model) N
  have quadratic := quadraticGuardedEventEnvelope_card_le (model := model)
    (LatticePairCandidateRecovery.Width N)
  have reset : (LatticePairRecoveryReset.resetEventEnvelope (model := model) N).card = 13 := by
    simp [LatticePairRecoveryReset.resetEventEnvelope, LatticePairRecoveryReset.nativeTrace,
      LatticePairRecoveryReset.cells, ResourcePool.ofList]
  simp only [LatticePairReusableRecovery.eventEnvelope, LatticePairFactorRecovery.eventEnvelope,
    Multiset.card_add, reset]
  exact Nat.add_le_add_left (Nat.add_le_add candidate quadratic) 13

/-- Cardinality of the complete independent native pool obeys the closed width ceiling. -/
theorem eventEnvelope_card_le (N : Nat) :
    (eventEnvelope (model := model) N).card ≤
      eventCountBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  have pair := reusable_card_le (model := model) N
  have pairCount : LatticePairRecoveryFold.PairCount = 120 := by
    norm_num [LatticePairRecoveryFold.PairCount, Nat.choose]
  have initialization : (QuadraticScratchInitialization.eventEnvelope (model := model) N).card =
      4 := rfl
  have seed : (LatticeEarlyFactorSeed.eventEnvelope (model := model) N).card = 5 := rfl
  have output : (LatticeBatchRecoveryOutput.eventEnvelope (model := model) N).card = 2 := rfl
  simp only [eventEnvelope, LatticeBatchRecoveryWorkspaceBody.eventEnvelope,
    LatticeSharedQuadraticInitialization.eventEnvelope, LatticeBatchRecoveryEndpoint.eventEnvelope,
    LatticeBatchRecoveryTail.eventEnvelope, LatticePairRecoveryFold.eventEnvelope,
    Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul, pairCount,
    modularSetupEventEnvelope_card_eq, initialization, seed, output]
  have scaled := Nat.mul_le_mul_left 120 pair
  unfold eventCountBound
  omega

omit [BitWord.Selected model] in
private theorem classicalWeight_le_card (pool : ResourcePool model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  induction pool using Multiset.induction_on with
  | empty => simp [ResourcePool.weightedCount]
  | cons event pool ih =>
      have eventBound : Resource.Event.classicalOperationWeight event ≤ 1 := by
        cases event <;> simp [Resource.Event.classicalOperationWeight]
      simp only [ResourcePool.weightedCount, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons] at ih ⊢
      omega

/-- Canonical classical-operation weight is bounded by the complete native event ceiling. -/
theorem eventEnvelope_classicalWeight_le (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope (model := model) N) ≤
      eventCountBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) :=
  (classicalWeight_le_card _).trans (eventEnvelope_card_le N)

variable {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Each complete allocated path inherits the independent ceiling from its actual native pool. -/
theorem into_eventCount_le (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (into ctx input parameter terminals result).Path) :
    ((into ctx input parameter terminals result).eventTrace path).length ≤
      eventCountBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) :=
  (Multiset.card_le_card (into_pool_le input parameter terminals result path)).trans
    (eventEnvelope_card_le N)

/-- Every literal classical operation is charged on that same complete allocated path. -/
theorem into_classicalWeight_le (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (into ctx input parameter terminals result).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((into ctx input parameter terminals result).resourcePool path) ≤
      eventCountBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) :=
  (classicalWeight_le_card _).trans (into_eventCount_le input parameter terminals result path)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedBatchRecoveryMachine
