/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Depth.Transform
import Mathlib.Algebra.BigOperators.Fin

/-!
# Weighted bounds from the same actual circuit path

The event pool obtained from the actual dependency expression equals the
pool of the same path's actual event trace. This identifies two existing
interpretations of the original circuit syntax. Its critical path therefore
lies below every independent coordinate-wise event allowance under arbitrary
natural durations. Tensor dependencies remain part of the original expression;
the weighted sum is an upper bound, not an alternative serial execution.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

noncomputable section

private lemma pool_flatten {model : ExecutionModel}
    (traces : List (List (Resource.Event model))) :
    ResourcePool.ofList traces.flatten = (traces.map ResourcePool.ofList).sum := by
  induction traces with
  | nil => rfl
  | cons trace traces ih => simp [ih]

private lemma pool_parallel {model : ExecutionModel}
    (events : List (Resource.Event model)) :
    DepthExpr.costEval (fun event => ResourcePool.singleton event)
        (events.foldr (fun event tail => .tensor (.atom event) tail) .id) =
      ResourcePool.ofList events := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      simp only [List.foldr_cons, DepthExpr.costEval_tensor, DepthExpr.costEval_atom,
        ResourcePool.ofList_cons, ih]

private lemma pool_mapSchedule {source target : ExecutionModel}
    (route : Resource.Event source → Resource.Event target)
    (expression : DepthExpr (Resource.Event source)) (trace : List (Resource.Event source))
    (agrees : DepthExpr.costEval (fun event => ResourcePool.singleton event) expression =
      ResourcePool.ofList trace) :
    DepthExpr.costEval (fun event => ResourcePool.singleton event)
        (DepthExpr.mapSchedule false route expression) = ResourcePool.ofList (trace.map route) := by
  let mapped : ResourcePool source →+ ResourcePool target :=
    { toFun := Multiset.map route
      map_zero' := rfl
      map_add' := Multiset.map_add route }
  have atoms : (fun event => ResourcePool.singleton (route event)) =
      mapped ∘ (fun event => ResourcePool.singleton event) := by
    funext event
    exact (Multiset.map_replicate route 1 event).symm
  rw [DepthExpr.costEval_mapSchedule]
  change DepthExpr.costEval (fun event => ResourcePool.singleton (route event)) expression = _
  rw [atoms, DepthExpr.costEval_mapAddMonoidHom, agrees]
  rfl

/-- Actual dependency syntax and actual event trace have exactly the same event pool. -/
lemma eventDepth_costEval_eq_resourcePool {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (path : code.Path) :
    DepthExpr.costEval (fun event => ResourcePool.singleton event) (code.eventDepth path) =
      code.resourcePool path := by
  induction code with
  | id | classical | classicalQuery | measureZ | retain => rfl
  | prepareZero => exact pool_parallel _
  | @unitary gates oracles ctx operations services allowAllocation program =>
      exact (program.resourcesFromEventDepth_eq_eventCost operations services).trans
        (UnitaryCircuit.ofList_eventTrace_eq_eventCost program operations services).symm
  | seq first second firstIH secondIH =>
      simp only [eventDepth, DepthExpr.costEval_seq, firstIH, secondIH,
        resourcePool, eventTrace, ResourcePool.ofList_append]
  | branch input body bodyIH => exact bodyIH path.1 path.2
  | iterate count body bodyIH =>
      simp only [eventDepth, DepthExpr.costEval_indexedProduct, DepthExpr.costEval_id,
        zero_add, bodyIH, resourcePool, eventTrace, pool_flatten, List.map_ofFn,
        List.sum_ofFn, Function.comp_def]
  | workspace ctx key shape fresh body bodyIH => exact bodyIH path
  | embed placement body bodyIH => exact bodyIH path
  | parallelClassical join separate first second firstIH secondIH
  | parallelQuantum join separate first second firstIH secondIH =>
      simp only [eventDepth, DepthExpr.costEval_tensor, resourcePool, eventTrace,
        ResourcePool.ofList_append]
      exact congrArg₂ (· + ·)
        (pool_mapSchedule _ _ _ (firstIH path.1))
        (pool_mapSchedule _ _ _ (secondIH path.2))

/-- Weighted total work from the actual dependency expression is the actual trace's weight. -/
lemma eventDepth_weightedCost_eq {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (duration : Resource.Event model → Nat) (path :
        code.Path) :
    DepthExpr.costEval duration (code.eventDepth path) =
      ResourcePool.weightedCount duration (code.resourcePool path) := by
  rw [DepthExpr.costEval_eq_weightedCount, eventDepth_costEval_eq_resourcePool]

/-- A coordinate-wise allowance bounds the same actual critical path under every duration. -/
lemma depth_le_weightedCount_of_pool_le {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (duration : Resource.Event model → Nat)
    (budget : ResourcePool model) (path : code.Path)
    (bounded : code.resourcePool path ≤ budget) :
    code.depth duration path ≤ ResourcePool.weightedCount duration budget :=
  (DepthExpr.depthEval_le_costEval duration (code.eventDepth path)).trans
    ((eventDepth_weightedCost_eq code duration path).trans_le
      (ResourcePool.weightedCount_mono duration bounded))

end

end QuantumAlg.Circuit
