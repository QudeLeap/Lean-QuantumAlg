/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program.Guarded

/-!
# Quadratic recovery cardinality bound

This module closes the optional quadratic-factor branch from its literal
fixed-width square-root, remainder-check, and first-success event envelopes.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeRecoveryResources

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory

noncomputable section

/-- Input-independent event-cardinality ceiling for one natural square root. -/
def natSqrtCardBound (inputWidth : Nat) : Nat :=
  6 * inputWidth + (inputWidth - 1) + 5

/-- Input-independent event-cardinality ceiling for one guarded quadratic
recovery. -/
def quadraticGuardedCardBound (shortWidth : Nat) : Nat :=
  38 + natSqrtCardBound (QuadraticPrefix.discriminantWidth shortWidth)

private theorem max_card_le_add {kind : ProblemKind} (left right : ResourcePool kind) :
    (ResourcePool.max left right).card ≤ left.card + right.card := by
  rw [← Multiset.card_add]
  exact Multiset.card_le_card (ResourcePool.max_le
    (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_left zero_le))

private theorem natSubEventEnvelope_card_le {kind : ProblemKind} (width : Nat) :
    (NatSub.eventEnvelope (kind := kind) width).card ≤ 3 := by
  have branchBound := max_card_le_add
    (ResourcePool.singleton
      (.classicalOperation (.wordBinary .bitXor width)))
    (ResourcePool.singleton
      (.classicalOperation (.wordBinary .sub width)) : ResourcePool kind)
  unfold NatSub.eventEnvelope
  rw [Multiset.card_add]
  simp only [ResourcePool.singleton, Multiset.card_replicate] at branchBound ⊢
  omega

private theorem natSqrtEventEnvelope_card_le {kind : ProblemKind}
    (inputWidth : Nat) :
    (NatSqrt.eventEnvelope (kind := kind) inputWidth).card ≤
      natSqrtCardBound inputWidth := by
  simp [NatSqrt.eventEnvelope, NatSqrt.initializationEventEnvelope,
    IntegerSqrt.roundTrace, ResourcePool.ofList, ResourcePool.singleton,
    ResourcePool.scale, natSqrtCardBound]
  omega

private theorem quadraticPrefixEventEnvelope_card_le {kind : ProblemKind}
    (shortWidth : Nat) :
    (QuadraticPrefix.eventEnvelope (kind := kind) shortWidth).card ≤
      natSqrtCardBound (QuadraticPrefix.discriminantWidth shortWidth) + 6 := by
  have subtractBound := natSubEventEnvelope_card_le
    (kind := kind) (QuadraticPrefix.discriminantWidth shortWidth)
  have sqrtBound := natSqrtEventEnvelope_card_le
    (kind := kind) (QuadraticPrefix.discriminantWidth shortWidth)
  unfold QuadraticPrefix.eventEnvelope QuadraticPrefix.discriminantEnvelope
  simp only [Multiset.card_add]
  simp only [ResourcePool.ofList, QuadraticPrefix.prepareTrace, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

private theorem quadraticCandidatesEventEnvelope_card_le {kind : ProblemKind}
    (shortWidth : Nat) :
    (QuadraticCandidates.eventEnvelope (kind := kind) shortWidth).card ≤
      natSqrtCardBound (QuadraticPrefix.discriminantWidth shortWidth) + 12 := by
  have prefixBound := quadraticPrefixEventEnvelope_card_le
    (kind := kind) shortWidth
  have subtractBound := natSubEventEnvelope_card_le
    (kind := kind) (QuadraticCandidates.candidateWidth shortWidth)
  unfold QuadraticCandidates.eventEnvelope QuadraticCandidates.suffixEnvelope
  simp only [Multiset.card_add]
  simp only [ResourcePool.singleton, Multiset.card_replicate, ResourcePool.ofList,
    QuadraticCandidates.resizeTrace, Multiset.coe_card, List.length_cons, List.length_nil]
  omega

private theorem selectionStepEventEnvelope_card_eq {kind : ProblemKind}
    (width : Nat) :
    (FirstAccepted.nativeEnvelope kind width).card = 4 :=
  FirstAccepted.firstAccepted_nativeEnvelope_card kind width

private theorem candidatePositiveEventEnvelope_card_eq {kind : ProblemKind}
    (shortWidth : Nat) :
    (QuadraticCandidateCheck.positiveEventEnvelope
      (kind := kind) shortWidth).card = 5 := by
  simp [QuadraticCandidateCheck.positiveEventEnvelope,
    NatModCheck.eventEnvelope, ResourcePool.singleton]

private theorem candidateCheckEventEnvelope_card_le {kind : ProblemKind}
    (shortWidth : Nat) :
    (QuadraticCandidateCheck.eventEnvelope
      (kind := kind) shortWidth).card ≤ 7 := by
  have branchBound := max_card_le_add
    (QuadraticCandidateCheck.positiveEventEnvelope
      (kind := kind) shortWidth)
    (ResourcePool.singleton (.classicalOperation (.bit .xor)))
  have positiveCard := candidatePositiveEventEnvelope_card_eq
    (kind := kind) shortWidth
  unfold QuadraticCandidateCheck.eventEnvelope
  rw [Multiset.card_add]
  simp only [ResourcePool.singleton, Multiset.card_replicate] at branchBound ⊢
  omega

private theorem candidateSelectEventEnvelope_card_le {kind : ProblemKind}
    (shortWidth : Nat) :
    (QuadraticCandidateSelect.eventEnvelope
      (kind := kind) shortWidth).card ≤ 11 := by
  have checkBound := candidateCheckEventEnvelope_card_le
    (kind := kind) shortWidth
  have selectionCard := selectionStepEventEnvelope_card_eq
    (kind := kind) (QuadraticCandidateCheck.CandidateWidth shortWidth)
  unfold QuadraticCandidateSelect.eventEnvelope
  rw [Multiset.card_add]
  omega

private theorem quadraticRecoveryMachineEventEnvelope_card_le
    {kind : ProblemKind} (shortWidth : Nat) :
    (QuadraticRecoveryMachine.eventEnvelope
      (kind := kind) shortWidth).card ≤
      natSqrtCardBound (QuadraticPrefix.discriminantWidth shortWidth) + 34 := by
  have candidatesBound := quadraticCandidatesEventEnvelope_card_le
    (kind := kind) shortWidth
  have selectBound := candidateSelectEventEnvelope_card_le
    (kind := kind) shortWidth
  unfold QuadraticRecoveryMachine.eventEnvelope
    QuadraticCandidatePairSelect.eventEnvelope
  simp only [Multiset.card_add]
  omega

/-- The actual guarded quadratic branch is bounded without adding an
unselected branch execution to the run. -/
theorem quadraticGuardedEventEnvelope_card_le {kind : ProblemKind}
    (shortWidth : Nat) :
    (QuadraticRecoveryGuarded.eventEnvelope
      (kind := kind) shortWidth).card ≤
      quadraticGuardedCardBound shortWidth := by
  have recoveryBound := quadraticRecoveryMachineEventEnvelope_card_le
    (kind := kind) shortWidth
  unfold QuadraticRecoveryGuarded.eventEnvelope
    QuadraticRecoveryReset.resetEventEnvelope QuadraticRecoveryReset.nativeTrace
    quadraticGuardedCardBound
  simp only [Multiset.card_add, ResourcePool.max, Multiset.union_zero]
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_cons, List.length_nil]
  omega

/-- The actual selected guarded execution satisfies the independent finite event-count bound. -/
theorem quadraticGuarded_eventCount_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : QuadraticRecoveryGuarded.Refs ctx shortWidth)
    (path : (QuadraticRecoveryGuarded.into refs).Path) :
    ((QuadraticRecoveryGuarded.into refs).eventTrace path).length ≤
      quadraticGuardedCardBound shortWidth := by
  change ((QuadraticRecoveryGuarded.into refs).resourcePool path).card ≤ _
  exact (Multiset.card_le_card (QuadraticRecoveryGuarded.into_pool_le refs path)).trans
    (quadraticGuardedEventEnvelope_card_le shortWidth)

end

end LatticeRecoveryResources
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
