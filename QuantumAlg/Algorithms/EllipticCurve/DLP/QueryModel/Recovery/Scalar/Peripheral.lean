/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Events
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Calibrated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.QuantumSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Calibrated

/-!
# Query, preparation and measurement observations on the same complete ECDLP path

These coordinates retain ordinary opaque group access, the actual initial
per-system preparation and both physical resets in every prescribed round.
All dimensions, widths and repetition counts remain symbolic.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every actual round reserves one ordinary opaque group-action query. -/
public theorem whole_budget_query_scalar (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    ResourcePool.count (model := Sampling.executionModel I A) (.oracle Coordinate.groupAction)
        (eventBudget I A expansion nontrivial count) ≤ count := by
  rw [whole_budget_nonclassical_count I A expansion nontrivial count
    (.oracle Coordinate.groupAction) (by intro label; simp), whole_initialization_budget]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton, reduceCtorEq,
    ↓reduceIte, mul_zero, zero_add]
  have per := (ResourcePool.le_iff_count.mp
    (reused_sampling_scalar_pool_le I A expansion)) (.oracle Coordinate.groupAction)
  simpa [ResourcePool.count_add, ResourcePool.count_singleton] using
    Nat.mul_le_mul_left count per

/-- Preparation is paid once for the original binary bank, with zero other dimensions. -/
public theorem whole_budget_preparation_scalar (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) (dimension : ℕ+) :
    ResourcePool.count (model := Sampling.executionModel I A) (.preparation dimension)
        (eventBudget I A expansion nontrivial count) ≤
      if 2 = dimension then Scalar.qubits (fieldWidth E) (scalarWidth I) else 0 := by
  have per := (ResourcePool.le_iff_count.mp
    (reused_sampling_scalar_pool_le I A expansion)) (.preparation dimension)
  have absent : ResourcePool.count (model := Sampling.executionModel I A)
      (.preparation dimension)
      (Sampling.Reuse.eventBudget I A expansion) = 0 :=
    Nat.eq_zero_of_le_zero (by
      simpa [ResourcePool.count_add, ResourcePool.count_singleton] using per)
  rw [whole_budget_nonclassical_count I A expansion nontrivial count
    (.preparation dimension) (by intro label; simp), absent, whole_initialization_budget,
    original_qubits_scalar]
  by_cases two : (2 : ℕ+) = dimension
  · subst dimension
    simp [ResourcePool.count_nsmul, ResourcePool.count_singleton]
  · simp [ResourcePool.count_nsmul, ResourcePool.count_singleton, two]

/-- Both complete resets and the exponent readouts are charged on every original real round. -/
public theorem whole_budget_measurement_scalar (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) (dimension : ℕ+) :
    ResourcePool.count (model := Sampling.executionModel I A) (.measurement dimension)
        (eventBudget I A expansion nontrivial count) ≤
      count * (if 2 = dimension then
        Scalar.roundMeasurements (fieldWidth E) (scalarWidth I) else 0) := by
  rw [whole_budget_nonclassical_count I A expansion nontrivial count
    (.measurement dimension) (by intro label; simp), whole_initialization_budget]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton, reduceCtorEq,
    ↓reduceIte, mul_zero, zero_add]
  have per := (ResourcePool.le_iff_count.mp
    (reused_sampling_scalar_pool_le I A expansion)) (.measurement dimension)
  rw [original_qubits_scalar] at per
  by_cases two : (2 : ℕ+) = dimension
  · subst dimension
    simpa [ResourcePool.count_add, ResourcePool.count_singleton, Scalar.roundMeasurements]
      using Nat.mul_le_mul_left count per
  · simpa [ResourcePool.count_add, ResourcePool.count_singleton, two, Ne.symm two]
      using Nat.mul_le_mul_left count per

/-- Supplementary quantum coordinates observe the same named calibrated algorithm path. -/
@[expose] public def PeripheralBounds (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (budget : Factoring.FailureBudget)
    (path : (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.Path) : Prop :=
  ResourcePool.count (model := Sampling.executionModel I A) (.oracle Coordinate.groupAction)
      ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤
    retryCountForBudget I budget ∧
  (∀ dimension : ℕ+,
    ResourcePool.count (model := Sampling.executionModel I A) (.preparation dimension)
        ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤
      if 2 = dimension then Scalar.qubits (fieldWidth E) (scalarWidth I) else 0) ∧
  (∀ dimension : ℕ+,
    ResourcePool.count (model := Sampling.executionModel I A) (.measurement dimension)
        ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤
      retryCountForBudget I budget * (if 2 = dimension then
        Scalar.roundMeasurements (fieldWidth E) (scalarWidth I) else 0))

/-- The actual full-run ledger supplies every supplementary scalar observation together. -/
public theorem calibrated_peripheralBounds (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (budget : Factoring.FailureBudget)
    (path : (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.Path) :
    PeripheralBounds I A expansion nontrivial budget path := by
  have pool := ResourcePool.le_iff_count.mp
    (ecdlpRecovery_code_events_le I A expansion nontrivial (retryCountForBudget I budget) path)
  exact ⟨(pool _).trans (whole_budget_query_scalar I A expansion nontrivial _),
    fun dimension => (pool _).trans
      (whole_budget_preparation_scalar I A expansion nontrivial _ dimension),
    fun dimension => (pool _).trans
      (whole_budget_measurement_scalar I A expansion nontrivial _ dimension)⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
