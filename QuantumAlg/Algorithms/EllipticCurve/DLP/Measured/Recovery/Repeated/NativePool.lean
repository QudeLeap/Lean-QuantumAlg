/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.RoundResources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.InitialSpace

/-!
# Native event pools for the selected repeated ECDLP circuit

The source sampler and one-time initialization execute without classical
operations. Their native events are embedded unchanged into the BitWord model
used by the interleaved checked-recovery tail.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- The promoted original round stays within its literal native quantum allowance. -/
theorem selectedSamplingRound_pool_le
    (path : (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed)).Path) :
    (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed)).resourcePool path ≤
        BitWord.liftQuantumPool (samplingRoundBudget E problem) := by
  let source := samplingRound E fieldTail sameWidth fits odd problem points seed
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  calc
    (BitWord.selectForCircuit source).resourcePool path =
        BitWord.liftQuantumPool (source.resourcePool original) := by
      simpa only [aligned] using BitWord.selectForCircuit_resourcePool source original
    _ ≤ BitWord.liftQuantumPool (samplingRoundBudget E problem) :=
      Multiset.map_le_map
        (samplingRound_pool_le E fieldTail sameWidth fits odd problem points seed original)

omit [Fact p.Prime] in
/-- The source initialization has exactly the literal zero-preparation and X-load pool. -/
theorem sourceInitial_pool_eq
    (path : (exponentRepeatedInitial E problem).Path) :
    (exponentRepeatedInitial E problem).resourcePool path =
      ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem)) := by
  change ResourcePool.ofList
    ((PublicInput.initializeWork E (orderWidth problem)).eventTrace path.1 ++
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace path.2) = _
  rw [PublicInput.initializeWork_eventTrace]
  have empty :
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace path.2 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [empty, List.append_nil]

omit [Fact p.Prime] in
/-- Selection preserves the exact one-time native initialization pool. -/
theorem selectedInitial_pool_eq
    (path : (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).Path) :
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).resourcePool path =
      BitWord.liftQuantumPool
        (ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem))) := by
  let source := exponentRepeatedInitial E problem
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  calc
    (BitWord.selectForCircuit source).resourcePool path =
        BitWord.liftQuantumPool (source.resourcePool original) := by
      simpa only [aligned] using BitWord.selectForCircuit_resourcePool source original
    _ = BitWord.liftQuantumPool
        (ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem))) :=
      congrArg BitWord.liftQuantumPool (sourceInitial_pool_eq E problem original)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
