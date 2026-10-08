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
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Calibrated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Cycle
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Independent scalar maximum depth of complete declared ECDLP computations

The actual initialized first computation, every reused checked computation and
zero-count terminal run have one parameter-only maximum. The total chronological
depth remains a separate bound and includes every prescribed real round.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem unit_weight_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun _ => 1) pool = pool.card := by
  simp [ResourcePool.weightedCount, Multiset.map_const']

/-- The maximum completed-cycle bound is independent of the real repetition count. -/
public theorem completeCycleDepth_scalar (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    completeCycleDepthLimit I A expansion nontrivial (fun _ => 1) ≤
      Scalar.maximumCycleDepth (fieldWidth E) (scalarWidth I) := by
  unfold completeCycleDepthLimit
  apply max_le
  · rw [unit_weight_card, firstRoundEventBudget, Multiset.card_add,
      whole_initialization_card_scalar]
    unfold Scalar.maximumCycleDepth
    exact (Nat.add_le_add_left (checked_round_events_scalar I A expansion nontrivial) _).trans
      (Nat.le_add_right _ 1)
  · rw [unit_weight_card]
    have total := whole_budget_events_scalar I A expansion nontrivial 0
    simp only [Scalar.wholeRunEvents, zero_mul, add_zero] at total
    unfold Scalar.maximumCycleDepth
    omega

/-- Every path of the actual calibrated public algorithm uses the same completed-cycle scalar. -/
public theorem calibrated_maximumCycleDepth_scalar (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed)
    (path : (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.Path) :
    (calibratedCycleCertificate I A expansion nontrivial budget wellFormed).maximumCycleDepth
        (fun _ => 1) path ≤ Scalar.maximumCycleDepth (fieldWidth E) (scalarWidth I) :=
  (ecdlpRecovery_cycleCertificate_maximumCycleDepth_le I A expansion nontrivial
    (retryCountForBudget I budget) (fun _ => 1) (fun _ => rfl) path).trans
      (completeCycleDepth_scalar I A expansion nontrivial)

/-- The separate chronological bound counts initialization, all actual rounds and final packing. -/
public theorem calibrated_wholeRunDepth_scalar (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (budget : Factoring.FailureBudget)
    (path : (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.Path) :
    (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.depth
        (fun _ => 1) path ≤
      Scalar.wholeRunEvents (fieldWidth E) (scalarWidth I) (retryCountForBudget I budget) := by
  have depth := Circuit.depth_le_weightedCount_of_pool_le
    (code I A expansion nontrivial (retryCountForBudget I budget)) (fun _ => 1)
    (eventBudget I A expansion nontrivial (retryCountForBudget I budget)) path
    (ecdlpRecovery_code_events_le I A expansion nontrivial (retryCountForBudget I budget) path)
  rw [unit_weight_card] at depth
  exact depth.trans (whole_budget_events_scalar I A expansion nontrivial
    (retryCountForBudget I budget))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
