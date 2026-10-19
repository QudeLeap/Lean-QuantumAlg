/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.LLL
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Candidate
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Quadratic
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Fold
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Selection.Seed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Tail
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Program

/-!
# Actual fixed-batch pair recovery cardinality bounds

The original finite scan and all `choose 16 2` reusable pair invocations are
charged on their actual paths. Independent width formulas retain the complete
LLL, nearest-plane, shared constants, modular setup, and quadratic work.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources

open Execution

noncomputable section

/-- Independent complete candidate recovery ceiling before the guarded factor branch. -/
def pairCandidateCardBound (modulusWidth m ell coordinateWidth : Nat) : Nat :=
  nearestPlaneSavedTargetCardBound m ell + (m + 3) + modularSetupCardBound modulusWidth +
    candidateScanCardBound modulusWidth coordinateWidth

/-- Independent complete reusable-pair ceiling includes all thirteen actual reset writes. -/
def reusablePairCardBound (modulusWidth m ell coordinateWidth : Nat) : Nat :=
  13 + (pairCandidateCardBound modulusWidth m ell coordinateWidth +
    quadraticGuardedCardBound coordinateWidth)

/-- Independent cardinality ceiling for shared initialization, all pairs, and output packing. -/
def fixedBatchRecoveryCardBound (modulusWidth m ell coordinateWidth : Nat) : Nat :=
  modularSetupCardBound modulusWidth + 11 +
    120 * reusablePairCardBound modulusWidth m ell coordinateWidth

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The complete actual pair-candidate path satisfies its independent public-width count bound. -/
lemma pairCandidate_eventCount_le (input : Input N)
    (refs : LatticePairCandidateRecovery.Refs ctx N)
    (path : (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs).Path) :
    ((LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs).eventTrace path).length ≤
      pairCandidateCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  have nearest := pairNearestSavedTarget_eventCount_le refs.pair path.1.1
  have constants := LatticeCandidateConstants.loadInto_eventCount
    (shortLogBits N) refs.constants path.1.2.1
  have setup := modularSetup_eventCount_le input refs.setup path.1.2.2
  have scan := initializedScan_eventCount_le input refs.scan path.2
  change _ ≤ candidateScanCardBound (modulusBits N) (LatticePairCandidateRecovery.Width N) at scan
  change ((LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs).resourcePool
    path).card ≤ _
  rw [LatticePairCandidateRecovery.pairCandidateRecoveryInto_resourcePool, Multiset.card_add,
    LatticePairCandidateRecovery.pairCandidatePrefix_resourcePool, Multiset.card_add,
    LatticePairCandidateRecovery.sharedInto_resourcePool, Multiset.card_add]
  change _ ≤ nearestPlaneSavedTargetCardBound (shortLogBits N) (tradeoffBits N) +
    (shortLogBits N + 3) + modularSetupCardBound (modulusBits N) +
      candidateScanCardBound (modulusBits N) (LatticePairCandidateRecovery.Width N)
  exact (Nat.add_le_add (Nat.add_le_add nearest
    (Nat.add_le_add constants.le setup)) scan).trans (by omega)

/-- Actual quadratic checking follows the complete actual candidate recovery in the same path. -/
lemma pairFactor_eventCount_le (input : Input N)
    (refs : LatticePairFactorRecovery.Refs ctx N)
    (path : (LatticePairFactorRecovery.into input refs).Path) :
    ((LatticePairFactorRecovery.into input refs).eventTrace path).length ≤
      pairCandidateCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) +
      quadraticGuardedCardBound (LatticePairCandidateRecovery.Width N) := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (pairCandidate_eventCount_le input refs.pair path.1)
    (quadraticGuarded_eventCount_le refs.quadratic path.2)

/-- Every reusable path pays the thirteen classical reset writes and then the full pair recovery. -/
lemma reusablePair_eventCount_le (input : Input N)
    (refs : LatticePairFactorRecovery.Refs ctx N)
    (path : (LatticePairReusableRecovery.into input refs).Path) :
    ((LatticePairReusableRecovery.into input refs).eventTrace path).length ≤
      reusablePairCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (LatticePairRecoveryReset.into_eventCount refs path.1).le
    (pairFactor_eventCount_le input refs path.2)

/-- All 120 actual pair invocations satisfy the original fixed finite-batch polynomial. -/
lemma pairFold_eventCount_le (input : Input N) (refs : LatticePairRecoveryFold.Refs ctx N)
    (path : (LatticePairRecoveryFold.into input refs).Path) :
    ((LatticePairRecoveryFold.into input refs).eventTrace path).length ≤
      120 * reusablePairCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  have folded := Circuit.forRange_eventCount_le LatticePairRecoveryFold.PairCount
    (fun index => LatticePairReusableRecovery.into input (refs.pair index))
    (reusablePairCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
      (LatticePairCandidateRecovery.Width N))
    (fun index => reusablePair_eventCount_le input (refs.pair index)) path
  have count : LatticePairRecoveryFold.PairCount = 120 := by
    norm_num [LatticePairRecoveryFold.PairCount, Nat.choose]
  simpa only [LatticePairRecoveryFold.into, count] using folded

/-- Actual early-factor widening and first-accepted selection pay at most five operations. -/
lemma earlyFactorSeed_eventCount_le (parameter : CInputRef ctx (ParameterShape N))
    (refs : LatticeEarlyFactorSeed.Refs ctx N)
    (path : (LatticeEarlyFactorSeed.into parameter refs).Path) :
    ((LatticeEarlyFactorSeed.into parameter refs).eventTrace path).length ≤ 5 := by
  have bound := Multiset.card_le_card (LatticeEarlyFactorSeed.into_pool_le parameter refs path)
  have envelopeCard : (LatticeEarlyFactorSeed.eventEnvelope (model := model) N).card = 5 := rfl
  rw [envelopeCard] at bound
  exact bound

/-- Shared initialization includes real target powering and all four quadratic constant writes. -/
lemma sharedInitialization_eventCount_le (input : Input N)
    (refs : LatticeSharedQuadraticInitialization.Refs ctx N)
    (path : (LatticeSharedQuadraticInitialization.into input refs).Path) :
    ((LatticeSharedQuadraticInitialization.into input refs).eventTrace path).length ≤
      modularSetupCardBound (modulusBits N) + 4 := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (modularSetup_eventCount_le input refs.setup path.1) (Nat.le_refl 4)

/-- The actual seeded tail executes all 120 pair invocations after the initial factor offer. -/
lemma batchTail_eventCount_le (input : Input N) (refs : LatticeBatchRecoveryTail.Refs ctx N)
    (path : (LatticeBatchRecoveryTail.into input refs).Path) :
    ((LatticeBatchRecoveryTail.into input refs).eventTrace path).length ≤
      5 + 120 * reusablePairCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (earlyFactorSeed_eventCount_le refs.parameter refs.seed path.1)
    (pairFold_eventCount_le input refs.fold path.2)

/-- Actual output packing is charged after the complete seeded batch. -/
lemma batchEndpoint_eventCount_le (input : Input N)
    (refs : LatticeBatchRecoveryEndpoint.Refs ctx N)
    (path : (LatticeBatchRecoveryEndpoint.into input refs).Path) :
    ((LatticeBatchRecoveryEndpoint.into input refs).eventTrace path).length ≤
      (5 + 120 * reusablePairCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N)) + 2 := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (batchTail_eventCount_le input refs.tail path.1)
    (LatticeBatchRecoveryOutput.into_eventCount refs.output path.2).le

/-- The same actual deepest body meets the independent full fixed-batch polynomial. -/
lemma batchBody_eventCount_le {root topCtx : RuntimeCtx model.kind} (input : Input N)
    (refs : LatticeBatchRecoveryWorkspaceBody.Refs root topCtx ctx N)
    (path : (LatticeBatchRecoveryWorkspaceBody.into input refs).Path) :
    ((LatticeBatchRecoveryWorkspaceBody.into input refs).eventTrace path).length ≤
      fixedBatchRecoveryCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  have bound := Nat.add_le_add
    (sharedInitialization_eventCount_le input
      (LatticeBatchRecoveryWorkspaceBody.initializationRefs refs) path.1)
    (batchEndpoint_eventCount_le input
      (LatticeBatchRecoveryWorkspaceBody.endpointRefs refs) path.2)
  exact bound.trans (by simp only [fixedBatchRecoveryCardBound]; omega)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources
