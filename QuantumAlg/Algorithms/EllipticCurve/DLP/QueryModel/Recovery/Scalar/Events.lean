/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.QuantumSpace
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Coordinates
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.QuantumSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-!
# Scalar resources of every actual finite declared ECDLP run

Generic preparation bounds dominate the actual native word. The original
checked recovery, two full-bank resets and terminal packing are charged in the
same full-run ledger. All widths and repetition counts remain symbolic.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private lemma classical_weight_le_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bounded := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event model => 1) (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bounded

/-- Both physical resets and the actual initialized word share one parameter-only event ceiling. -/
public lemma reused_sampling_events_scalar (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (Sampling.Reuse.eventBudget I expansion).card ≤
      Scalar.roundSingleQubit (fieldWidth E) (scalarWidth I) +
        Scalar.roundCnot (scalarWidth I) + 1 +
          Scalar.roundMeasurements (fieldWidth E) (scalarWidth I) := by
  have bound := Multiset.card_le_card (reused_sampling_scalar_pool_le I expansion)
  rw [original_qubits_scalar] at bound
  simpa only [Multiset.card_add, ResourcePool.singleton, Multiset.card_replicate,
    Scalar.roundSingleQubit, Scalar.roundCnot, Scalar.roundMeasurements] using bound

/-- One complete actual checked round is bounded before any fixed-instance substitution. -/
public lemma checked_round_events_scalar (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    (roundEventBudget I expansion nontrivial).card ≤
      Scalar.roundEvents (fieldWidth E) (scalarWidth I) := by
  rw [roundEventBudget, Multiset.card_add]
  unfold Scalar.roundEvents Scalar.recoveryEvents
  exact Nat.add_le_add (reused_sampling_events_scalar I expansion)
    (attemptEnvelope_card_le (Sampling.executionModel I) (curve E) (modulus I nontrivial))

/-- Every prepared system contributes one event to the actual initialization ledger. -/
public lemma whole_initialization_card_scalar (I : ECDLPInstance E) :
    (initializationBudget I).card = Scalar.qubits (fieldWidth E) (scalarWidth I) := by
  rw [whole_initialization_budget, Multiset.card_nsmul, ResourcePool.singleton,
    Multiset.card_replicate, Nat.mul_one, original_qubits_scalar]

/-- The complete independent ledger has a scalar ceiling linear in the actual count. -/
public lemma whole_budget_events_scalar (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    (eventBudget I expansion nontrivial count).card ≤
      Scalar.wholeRunEvents (fieldWidth E) (scalarWidth I) count := by
  have checked := checked_round_events_scalar I expansion nontrivial
  rw [roundEventBudget, Multiset.card_add] at checked
  simp only [eventBudget, tailEventBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
    ResourcePool.scale, Multiset.card_add, Multiset.card_nsmul,
    ResourcePool.ofList, Multiset.coe_card, List.length_cons, List.length_nil]
  rw [whole_initialization_card_scalar]
  unfold Scalar.wholeRunEvents
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left count checked) _) 1

/-- All native gates are bounded by the generic width ceiling of each original real round. -/
public lemma whole_budget_gate_scalar (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Sampling.executionModel I) (.gate coordinate)
        (eventBudget I expansion nontrivial count) ≤
      count * (match coordinate with
        | .singleQubit => Scalar.roundSingleQubit (fieldWidth E) (scalarWidth I)
        | .cnot => Scalar.roundCnot (scalarWidth I)
        | .toffoli => 0) := by
  rw [whole_budget_nonclassical_count I expansion nontrivial count (.gate coordinate)
    (by intro label; simp), whole_initialization_budget]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton, reduceCtorEq,
    ↓reduceIte, mul_zero, zero_add]
  have per := (ResourcePool.le_iff_count.mp
    (reused_sampling_scalar_pool_le I expansion)) (.gate coordinate)
  rw [original_qubits_scalar] at per
  cases coordinate <;>
    simpa [ResourcePool.count_add, ResourcePool.count_singleton,
      Scalar.roundSingleQubit, Scalar.roundCnot] using Nat.mul_le_mul_left count per

/-- Quantum initialization has zero classical weight; every actual attempt and final pack count. -/
public lemma whole_budget_classical_scalar (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (eventBudget I expansion nontrivial count) ≤
      count * Scalar.recoveryEvents (fieldWidth E) (scalarWidth I) + 1 := by
  rw [whole_budget_classical_count, whole_initialization_budget]
  simp only [ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.classicalOperationWeight, mul_zero, zero_add]
  unfold Scalar.recoveryEvents
  exact Nat.add_le_add_right (Nat.mul_le_mul_left count
    ((classical_weight_le_card _).trans
      (attemptEnvelope_card_le (Sampling.executionModel I) (curve E) (modulus I nontrivial)))) 1

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
