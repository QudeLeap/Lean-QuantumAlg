/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.RoundResources

/-!
# Actual ECDLP sampling-round event ceiling

The source round's path is bounded by its exact reset and sampling ledger.
Selecting the native bit/word language for the following recovery preserves
both the actual path choices and the number of native quantum events.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP ConcreteCircuitAccess MeasuredUncompute

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- Literal reset and original sampling ledger for one complete reused round. -/
def samplingRoundEventBound : Nat :=
  (samplingRoundBudget E problem).card

/-- The selected original round path stays within that literal ledger. -/
theorem samplingRound_eventCount_le
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    ((samplingRound E fieldTail sameWidth fits odd problem points seed).eventTrace path).length ≤
      samplingRoundEventBound E problem :=
  Multiset.card_le_card
    (samplingRound_pool_le E fieldTail sameWidth fits odd problem points seed path)

/-- The promoted round has the same finite native event count as its source path. -/
theorem selectedSamplingRound_eventCount_le
    (path : (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed)).Path) :
    ((BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed)).eventTrace path).length ≤
      samplingRoundEventBound E problem := by
  let source := samplingRound E fieldTail sameWidth fits odd problem points seed
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  calc
    ((BitWord.selectForCircuit source).eventTrace path).length =
        (source.eventTrace original).length := by
      simpa only [aligned] using BitWord.selectForCircuit_eventCount source original
    _ ≤ samplingRoundEventBound E problem :=
      samplingRound_eventCount_le E fieldTail sameWidth fits odd problem points seed original

omit [Fact p.Prime] in
/-- Selecting the classical language preserves the exact one-time initialization trace length. -/
theorem selectedInitial_eventCount
    (path : (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).Path) :
    ((BitWord.selectForCircuit (exponentRepeatedInitial E problem)).eventTrace path).length =
      (Allocation.initializationTrace p (2 * orderWidth problem)).length := by
  let initial := exponentRepeatedInitial E problem
  let sourcePath := (BitWord.selectForCircuitPathEquiv initial).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv initial) sourcePath = path :=
    (BitWord.selectForCircuitPathEquiv initial).apply_symm_apply path
  have same := BitWord.selectForCircuit_eventCount initial sourcePath
  rw [aligned] at same
  rw [same]
  change List.length
    ((PublicInput.initializeWork E (orderWidth problem)).eventTrace sourcePath.1 ++
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace sourcePath.2) =
    (Allocation.initializationTrace p (2 * orderWidth problem)).length
  rw [List.length_append, PublicInput.initializeWork_eventTrace]
  have empty :
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace sourcePath.2 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [empty]
  simp

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
