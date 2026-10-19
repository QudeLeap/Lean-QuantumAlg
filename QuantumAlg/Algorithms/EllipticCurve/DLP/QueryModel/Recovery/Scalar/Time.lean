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
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First

/-!
# Independent whole-run depth of the declared ECDLP computation

The chronological bound includes initialization, every prescribed round and packing.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private lemma unit_weight_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun _ => 1) pool = pool.card := by
  simp [ResourcePool.weightedCount, Multiset.map_const']

/-- The separate chronological bound counts initialization, all actual rounds and final packing. -/
public lemma calibrated_wholeRunDepth_scalar (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (budget : Factoring.FailureBudget)
    (path : (calibratedWholeAlgorithm I expansion nontrivial budget).run.code.Path) :
    (calibratedWholeAlgorithm I expansion nontrivial budget).run.code.depth
        (fun _ => 1) path ≤
      Scalar.wholeRunEvents (fieldWidth E) (scalarWidth I) (retryCountForBudget I budget) := by
  have depth := Circuit.depth_le_weightedCount_of_pool_le
    (code I expansion nontrivial (retryCountForBudget I budget)) (fun _ => 1)
    (eventBudget I expansion nontrivial (retryCountForBudget I budget)) path
    (ecdlpRecovery_code_events_le I expansion nontrivial (retryCountForBudget I budget) path)
  rw [unit_weight_card] at depth
  exact depth.trans (whole_budget_events_scalar I expansion nontrivial
    (retryCountForBudget I budget))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
