/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Depth.WeightedCost
import Mathlib.Algebra.BigOperators.Fin

/-!
# Weighted bounds from the same actual circuit path

The native pool obtained from the actual dependency expression equals the
pool of the same path's actual event trace. This identifies two existing
interpretations of the original circuit syntax. Its critical path therefore
lies below every independent coordinate-wise event allowance under arbitrary
natural durations. Tensor dependencies remain part of the original expression;
the weighted sum is an upper bound, not an alternative serial execution.
-/

namespace QuantumAlg.Circuit

noncomputable section

private theorem pool_flatten {kind : ProblemKind}
    (traces : List (List (Resource.Event kind))) :
    ResourcePool.ofList traces.flatten = (traces.map ResourcePool.ofList).sum := by
  induction traces with
  | nil => rfl
  | cons trace traces ih => simp [ih]

/-- Actual dependency syntax and actual event trace have exactly the same native pool. -/
theorem eventDepth_costEval_eq_resourcePool {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (path : code.Path) :
    DepthExpr.costEval (fun event => ResourcePool.singleton event) (code.eventDepth path) =
      code.resourcePool path := by
  induction code with
  | id | classical | declaredCall | measureZ | randomBits | retain | prepare => rfl
  | unitary program placement =>
      exact program.resourcesFromEventDepth_eq_eventCost.trans
        (UnitaryCircuit.ofList_eventTrace_eq_eventCost program).symm
  | seq first second firstIH secondIH =>
      simp only [eventDepth, DepthExpr.costEval_seq, firstIH, secondIH,
        resourcePool, eventTrace, ResourcePool.ofList_append]
  | branch input body bodyIH => exact bodyIH path.1 path.2
  | iterate count body bodyIH =>
      simp only [eventDepth, DepthExpr.costEval_indexedProduct, DepthExpr.costEval_id,
        zero_add, bodyIH, resourcePool, eventTrace, pool_flatten, List.map_ofFn,
        List.sum_ofFn, Function.comp_def]
  | workspace ctx key shape fresh body bodyIH => exact bodyIH path

/-- Weighted total work from the actual dependency expression is the actual trace's weight. -/
theorem eventDepth_weightedCost_eq {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (duration : Resource.Event kind → Nat) (path : code.Path) :
    DepthExpr.costEval duration (code.eventDepth path) =
      ResourcePool.weightedCount duration (code.resourcePool path) := by
  rw [DepthExpr.costEval_eq_weightedCount, eventDepth_costEval_eq_resourcePool]

/-- A coordinate-wise allowance bounds the same actual critical path under every duration. -/
theorem depth_le_weightedCount_of_pool_le {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (duration : Resource.Event kind → Nat)
    (budget : ResourcePool kind) (path : code.Path)
    (bounded : code.resourcePool path ≤ budget) :
    code.depth duration path ≤ ResourcePool.weightedCount duration budget :=
  (DepthExpr.depthEval_le_costEval duration (code.eventDepth path)).trans
    ((eventDepth_weightedCost_eq code duration path).trans_le
      (ResourcePool.weightedCount_mono duration bounded))

end

end QuantumAlg.Circuit
