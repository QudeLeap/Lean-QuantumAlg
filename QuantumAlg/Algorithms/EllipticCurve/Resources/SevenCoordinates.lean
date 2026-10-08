/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Solves
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Complete
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Complete
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Cycle
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Space
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Seven scalar coordinates of one actual arbitrary-width ECC path

All mathematical parameters and repetition counts remain symbolic. Native
counts, physical memory and certified complete-cycle depth observe the same
named actual run. Classical resident and auxiliary bits retain the original
widened XGCD implementation, using its proved quadratic width ceiling.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
  (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
  (seed : AffinePoint E) (addends : AddendEncoding E I points)
  (count : Nat) (failure : ℝ)

/-- Seven parameter-only ceilings on the same original ECC execution path.
Both classical storage roles and every quantum dimension remain explicit. -/
@[expose] public def SevenCoordinateBounds
    (cycles : Algorithm.CycleSolves
      (algorithm E fieldTail sameWidth fits odd I points seed count)
      (completeCycleProblem E fieldTail sameWidth fits I points seed addends count failure))
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    Prop :=
  (∀ dimension : ℕ+,
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakResidentSpace
      path (.quantumSystems dimension) ≤
        if 2 = dimension then Scalar.qubits p.size (orderWidth (ECDLP.Canonical.problem I))
        else 0) ∧
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakAuxiliarySpace
      path (.quantumSystems dimension) ≤
        if 2 = dimension then Scalar.qubits p.size (orderWidth (ECDLP.Canonical.problem I))
        else 0)) ∧
  ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .toffoli)
      ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
        count * Scalar.roundToffoli p.size (orderWidth (ECDLP.Canonical.problem I)) ∧
  ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .cnot)
      ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
        count * Scalar.roundCnot p.size (orderWidth (ECDLP.Canonical.problem I)) ∧
  ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .singleQubit)
      ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
        Scalar.loadBits p.size +
          count * Scalar.roundSingle p.size (orderWidth (ECDLP.Canonical.problem I)) ∧
  cycles.maximumCycleDepth (fun _ => 1) path ≤
    Scalar.maximumCycleDepth p.size (Nat.clog 2 p)
      (orderWidth (ECDLP.Canonical.problem I)) ∧
  (((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakResidentSpace
      path .classicalBits ≤ Scalar.residentBits p.size (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I))) ∧
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakAuxiliarySpace
      path .classicalBits ≤ Scalar.auxiliaryBits p.size (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I)))) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
      count * Scalar.recoveryEvents (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I)) + 1

/-- Each real path of the calibrated original ECC algorithm consumes all seven generic bounds. -/
public theorem algorithm_sevenCoordinates
    (calibrated : RepetitionCondition E I points seed count failure)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    SevenCoordinateBounds E fieldTail sameWidth fits odd I points seed addends count failure
      (completeCycleCertificate E fieldTail sameWidth fits odd I points seed addends count
        failure calibrated) path := by
  have pool := exponentRepeatedRun_pool_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  have resident := exponentRepeatedRun_resident_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  have auxiliary := exponentRepeatedRun_auxiliary_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    constructor
    · exact (resident (.quantumSystems dimension)).trans_eq
        (quantumSystems_scalar_eq E I count dimension)
    · exact (auxiliary (.quantumSystems dimension)).trans_eq
        (auxiliaryQuantumSystems_scalar_eq E I count dimension)
  · exact (Multiset.count_le_of_le _ pool).trans
      (repeatedRun_toffoli_scalar E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le count)
  · exact (Multiset.count_le_of_le _ pool).trans
      (repeatedRun_cnot_scalar E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le count)
  · exact (Multiset.count_le_of_le _ pool).trans
      (repeatedRun_singleQubit_scalar E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le count)
  · exact (algorithm_completeMaximumCycleDepth_le E fieldTail sameWidth fits odd I
      points seed addends count failure calibrated path).trans (completeCycleDepth_scalar_le E I)
  · exact ⟨(resident .classicalBits).trans (residentBits_scalar_le E I count),
      (auxiliary .classicalBits).trans (auxiliaryBits_scalar_le E I count)⟩
  · exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight pool).trans
      (repeatedRun_classicalOperations_scalar E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le count)

/-- Whole chronological depth remains a separate scalar bound, linear in the actual count. -/
public theorem algorithm_wholeRunDepth_scalar
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.depth
        (fun _ => 1) path ≤
      Scalar.wholeRunEvents p.size (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I)) count := by
  have depth := exponentRepeatedRun_depth_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count (fun _ => 1) path
  rw [scalar_unitWeight_card] at depth
  exact depth.trans (repeatedRun_events_scalar E (ECDLP.Canonical.problem I)
    I.subgroupOrder_prime.two_le count)

end

end QuantumAlg.EllipticCurve.LogicalResources
