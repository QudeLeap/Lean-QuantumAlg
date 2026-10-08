/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan.Initialized.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Basic

/-!
# Actual candidate-scan cardinality bounds

The fixed three-dimensional scan visits all `85 * 69^2` original coefficient
slots. The independent polynomial includes each slot's actual modulus loading,
square-and-multiply operations, and direct first-accepted selection. Finite-list
induction uses the public offset bounds without evaluating the full scan.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources

open Execution ClassicalRoutines

noncomputable section

/-- Exact number of candidate slots in the original nearest-plane window. -/
def candidateScanWork : Nat := 85 * 69 ^ 2

/-- Independent slot ceiling includes literal modulus loading even at zero exponent width. -/
def candidateSlotCardBound (modulusWidth coordinateWidth : Nat) : Nat :=
  179 + 2 * modulusWidth + 6 * coordinateWidth

/-- Independent ceiling for clearing the latch and executing every original candidate slot. -/
def candidateScanCardBound (modulusWidth coordinateWidth : Nat) : Nat :=
  1 + candidateScanWork * candidateSlotCardBound modulusWidth coordinateWidth

private theorem prefixTrace_length {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat)
    (offset : NumberTheory.IntegerPoint3) :
    (LatticeCandidateDistancePrefix.prefixTrace (model := model) width offset).length =
      LatticeOffsetMaterializer.operationCount offset + 26 := by
  simp [LatticeCandidateDistancePrefix.prefixTrace, LatticeOffsetMaterializer.offsetTrace,
    ConstantWord.Signed.nativeTrace, ConstantWord.Signed.loopTrace,
    LatticeCandidatePointMachine.candidateTrace, LatticeCandidatePointMachine.coordinateTrace,
    LatticePointDifferenceMachine.differenceTrace,
    LatticeSquaredDistanceMachine.distanceTrace, LatticeOffsetMaterializer.operationCount]
  omega

private theorem exponentEnvelope_card_le {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat) :
    (LatticeCandidateSlotMachine.exponentEnvelope model width).card ≤ 19 := by
  have bound := poolMax_card_le_add
    (ResourcePool.ofList (LatticeCandidateExponent.exponentTrace (model := model) width false))
    (ResourcePool.ofList (LatticeCandidateExponent.exponentTrace width true))
  simpa [LatticeCandidateSlotMachine.exponentEnvelope, LatticeCandidateExponent.exponentTrace,
    LatticeCandidateExponent.suffixTrace, NumberTheory.SignedWord.signTrace,
    NumberTheory.SignedWord.magnitudeTrace, ResourcePool.ofList] using bound

/-- Every original bounded coefficient offset has the independent complete native slot ceiling. -/
theorem candidateSlotEventEnvelope_card_le {model : ExecutionModel} [BitWord.Selected model]
    (modulusWidth coordinateWidth : Nat) (offset : NumberTheory.IntegerPoint3)
    (offsetBound : offset.1.natAbs + offset.2.1.natAbs + offset.2.2.natAbs ≤ 110) :
    (LatticeCandidateSlotMachine.candidateSlotEventEnvelope model coordinateWidth modulusWidth
      offset).card ≤ candidateSlotCardBound modulusWidth coordinateWidth := by
  have exponentBound := exponentEnvelope_card_le (model := model) coordinateWidth
  have powerCard := powerEventEnvelope_card_eq (model := model) modulusWidth coordinateWidth
  have prefixCard := prefixTrace_length (model := model) coordinateWidth offset
  unfold LatticeCandidateSlotMachine.candidateSlotEventEnvelope
    LatticeCandidatePowerMachine.candidatePowerEventEnvelope
    LatticeCandidateSelector.candidateSelectorEventEnvelope candidateSlotCardBound
  simp only [Multiset.card_add]
  simp only [ResourcePool.ofList, Multiset.coe_card] at prefixCard ⊢
  rw [prefixCard, powerCard]
  unfold powerCardBound
  simp only [LatticeNearTargetScale.scaleTrace, LatticeNearTargetScale.copyScaleTrace,
    LatticeCandidateSelector.eligibilityTrace, FirstAccepted.Direct.copyTrace,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    ResourcePool.singleton,
    Multiset.card_replicate]
  unfold LatticeOffsetMaterializer.operationCount
  omega

private theorem offset_natAbs_sum_le (offset : NumberTheory.IntegerPoint3)
    (member : offset ∈ LatticeCandidateScan.offsets.toList) :
    offset.1.natAbs + offset.2.1.natAbs + offset.2.2.natAbs ≤ 110 := by
  rw [LatticeCandidateScan.offsets, NumberTheory.toList_coefficientOffsetVector3,
    NumberTheory.mem_coefficientOffsetList3, NumberTheory.mem_coefficientOffsetBox3] at member
  change -(42 : Int) ≤ offset.1 ∧ offset.1 ≤ 42 ∧
    -(34 : Int) ≤ offset.2.1 ∧ offset.2.1 ≤ 34 ∧
      -(34 : Int) ≤ offset.2.2 ∧ offset.2.2 ≤ 34 at member
  have abs_le (value : Int) (bound : Nat)
      (lower : -(bound : Int) ≤ value) (upper : value ≤ (bound : Int)) :
      value.natAbs ≤ bound := by
    cases value <;> omega
  have first := abs_le offset.1 42 member.1 member.2.1
  have second := abs_le offset.2.1 34 member.2.2.1 member.2.2.2.1
  have third := abs_le offset.2.2 34 member.2.2.2.2.1 member.2.2.2.2.2
  omega

private theorem offsetsEventEnvelope_card_le {model : ExecutionModel} [BitWord.Selected model]
    (modulusWidth coordinateWidth : Nat) (items : List NumberTheory.IntegerPoint3)
    (bounded : ∀ offset ∈ items,
      offset.1.natAbs + offset.2.1.natAbs + offset.2.2.natAbs ≤ 110) :
    (LatticeCandidateScan.offsetsEventEnvelope model coordinateWidth modulusWidth items).card ≤
      items.length * candidateSlotCardBound modulusWidth coordinateWidth := by
  induction items with
  | nil => simp [LatticeCandidateScan.offsetsEventEnvelope]
  | cons offset tail inductionHypothesis =>
    rw [LatticeCandidateScan.offsetsEventEnvelope, Multiset.card_add]
    have first := candidateSlotEventEnvelope_card_le (model := model) modulusWidth coordinateWidth
      offset (bounded offset (List.mem_cons_self))
    have later := inductionHypothesis (fun item member =>
      bounded item (List.mem_cons_of_mem offset member))
    simpa only [List.length_cons, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add first later

/-- The complete scan envelope obeys the polynomial without expanding its 404,685 slots. -/
theorem scanEventEnvelope_card_le {model : ExecutionModel} [BitWord.Selected model]
    (modulusWidth coordinateWidth : Nat) :
    (LatticeCandidateScan.scanEventEnvelope model coordinateWidth modulusWidth).card ≤
      candidateScanWork * candidateSlotCardBound modulusWidth coordinateWidth := by
  have bound := offsetsEventEnvelope_card_le (model := model) modulusWidth coordinateWidth
    LatticeCandidateScan.offsets.toList offset_natAbs_sum_le
  have count : LatticeCandidateScan.offsets.toList.length = candidateScanWork := by
    rw [List.Vector.toList_length]
    exact NumberTheory.nearestPlaneCoefficientBounds3_work
  simpa only [LatticeCandidateScan.scanEventEnvelope, count] using bound

/-- Latch initialization and the complete independent scan envelope satisfy the closed ceiling. -/
theorem initializedScanEventEnvelope_card_le {model : ExecutionModel} [BitWord.Selected model]
    (N m ell : Nat) :
    (LatticeCandidateScanInitialized.initializedScanEventEnvelope model N m ell).card ≤
      candidateScanCardBound (modulusBits N) (RSA.ShortLogWidths.coordinateWidth N m ell) := by
  have bound := scanEventEnvelope_card_le (model := model) (modulusBits N)
    (RSA.ShortLogWidths.coordinateWidth N m ell)
  unfold LatticeCandidateScanInitialized.initializedScanEventEnvelope candidateScanCardBound
  rw [Multiset.card_add]
  simpa only [LatticeCandidateSelectorInit.clearAcceptedEventEnvelope, ResourcePool.singleton,
    Multiset.card_replicate] using Nat.add_le_add_left bound 1

/-- Actual complete scan paths satisfy the independent polynomial in native event count. -/
theorem initializedScan_eventCount_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {N m ell : Nat} (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (path : (LatticeCandidateScanInitialized.initializedScanInto input refs).Path) :
    ((LatticeCandidateScanInitialized.initializedScanInto input refs).eventTrace path).length ≤
      candidateScanCardBound (modulusBits N) (RSA.ShortLogWidths.coordinateWidth N m ell) := by
  change ((LatticeCandidateScanInitialized.initializedScanInto input refs).resourcePool
    path).card ≤ _
  exact (Multiset.card_le_card
    (LatticeCandidateScanInitialized.initializedScanInto_pool_le input refs path)).trans
      (initializedScanEventEnvelope_card_le N m ell)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources
