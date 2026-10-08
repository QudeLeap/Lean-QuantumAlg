/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Resources
public import QuantumAlg.Components.Classical.Model.BitWord.Promotion.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Resources
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates

/-! # Symbolic native coordinates of the original complete ECC event allowance -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP ScalarMultiplication.MeasuredPlacement
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open BitWord

theorem repeatedRunBudget_gate_count {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    (problem : FiniteCyclicDLP.KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (count : Nat)
    (gate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate gate) (PrimeFieldShortWeierstrass.ECDLP.Measured.repeatedRunBudget
        E problem nontrivial count) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate gate) (ResourcePool.ofList
          (Allocation.initializationTrace
            p (2 * FiniteCyclicDLP.orderWidth problem))) +
      count * ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate gate) (PrimeFieldShortWeierstrass.ECDLP.Measured.samplingRoundBudget E problem) := by
  have outside : ∀ label,
      (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty BitWord.model) gate) ≠
        .classicalOperation label := by
    intro label
    simp
  have attempt_zero :=
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.attemptEnvelope_count_eq_zero
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate gate) outside
      (PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout.curveSpec E)
      (PrimeFieldShortWeierstrass.ECDLP.Measured.recoveryModulusSpec problem nontrivial)
  simp only [PrimeFieldShortWeierstrass.ECDLP.Measured.repeatedRunBudget,
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.sampledRecoveryEnvelope,
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.sampledAttemptsEnvelope,
    ResourcePool.count_add, ResourcePool.count_scale, attempt_zero,
    liftQuantumPool_gate_count]
  simp

theorem zeroPreparation_gate_count (gate : AlgorithmGate.Coordinate)
    {count : Nat} (layout : QuantumLayout count) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate gate) (ResourcePool.ofList
        (ZeroPreparation.eventTrace AlgorithmGate.model .empty layout)) = 0 := by
  simp [ZeroPreparation.eventTrace, ResourcePool.count_ofList,
    List.count_eq_zero, List.mem_ofFn]

theorem initialization_gate_count (modulus count : Nat)
    (gate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate gate) (ResourcePool.ofList
        (Allocation.initializationTrace
          modulus count)) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate gate) (MeasuredUncompute.InPlacePreparation.loadProgram modulus).eventCost := by
  simp only [Allocation.initializationTrace,
    ResourcePool.ofList_append, ResourcePool.count_add,
    zeroPreparation_gate_count, zero_add, add_zero]
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]

theorem load_pool (modulus : Nat) :
    (MeasuredUncompute.InPlacePreparation.loadProgram modulus).eventCost =
      EncodedBit.Word.BasisLoad.xCount
        (MeasuredUncompute.InPlacePreparation.loadConstant modulus) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit) := by
  exact (Execution.PreparationLoaded.program_eventCost
    (MAU.Inversion.SharedEEA.InversePreparation.before modulus.size)
    MAU.Inversion.SharedEEA.InversePreparation.auxiliaryKey
    (MAU.Inversion.SharedEEA.InputPreparation.auxiliaryLayout modulus.size)
    (MAU.Inversion.SharedEEA.InversePreparation.auxiliary_fresh modulus.size)
    (MAU.Inversion.SharedEEA.InversePreparation.auxiliary_disjoint modulus.size) _).trans
      (EncodedBit.Word.BasisLoad.basisLoad_eventCost
        (MAU.Inversion.SharedEEA.InputPreparation.auxiliaryQubitLayout modulus.size) .empty
        (MeasuredUncompute.InPlacePreparation.loadConstant modulus))

theorem classicalWeight_le_card
    (pool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model)) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bounded := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model) => 1)
    (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bounded

theorem repeatedRunBudget_classicalWeight {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    (known : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ known.order)
    (count : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ECDLP.Measured.repeatedRunBudget E known nontrivial count) =
      count * ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
          (ECDLP.Canonical.Layout.curveSpec E)
          (ECDLP.Measured.recoveryModulusSpec known nontrivial)) + 1 := by
  simp only [ECDLP.Measured.repeatedRunBudget, sampledRecoveryEnvelope,
    sampledAttemptsEnvelope, ResourcePool.scale, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, liftQuantumPool_classicalWeight_zero]
  simp [Resource.Event.classicalOperationWeight]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
