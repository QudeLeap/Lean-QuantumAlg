/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Depth.Expr
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weighted total cost from the same expression's model-selected event pool

Summing the event weights after collecting a syntactic expression's event
coordinates gives its total cost. Coordinatewise domination by an independent
pool therefore bounds every nonnegative duration assignment and, in
particular, the expression's critical path. No gate expansion or resource
conversion occurs in this arithmetic bridge.
-/

namespace QuantumAlg.ResourcePool

/-- A literal coordinatewise event budget dominates every natural-number weighted observation. -/
theorem weightedCount_mono {model : ExecutionModel} (weight : Resource.Event model → Nat)
    {actual budget : ResourcePool model} (bounded : actual ≤ budget) :
    weightedCount weight actual ≤ weightedCount weight budget := by
  obtain ⟨remainder, rfl⟩ := exists_add_of_le bounded
  rw [weightedCount_add]
  exact Nat.le_add_right _ _

/-- Weighted observation commutes with a finite sum of strict event pools. -/
theorem weightedCount_sum {model : ExecutionModel} {ι : Type}
    (weight : Resource.Event model → Nat) (indices : Finset ι)
    (pool : ι → ResourcePool model) :
    weightedCount weight (∑ index ∈ indices, pool index) =
      ∑ index ∈ indices, weightedCount weight (pool index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, weightedCount_zero]
  | @insert index indices absent ih =>
      simp only [Finset.sum_insert absent, weightedCount_add, ih]

end QuantumAlg.ResourcePool

namespace QuantumAlg.DepthExpr

/-- Total syntactic cost is exactly the weighted observation of that syntax's strict event pool. -/
theorem costEval_eq_weightedCount {model : ExecutionModel}
    (assign : Resource.Event model → Nat) (expression : DepthExpr (Resource.Event model)) :
    costEval assign expression = ResourcePool.weightedCount assign
      (costEval (fun event => ResourcePool.singleton event) expression) := by
  induction expression with
  | id => rfl
  | atom event => simp only [costEval_atom, ResourcePool.weightedCount_singleton, Nat.one_mul]
  | seq left right leftIH rightIH =>
      simp only [costEval_seq, ResourcePool.weightedCount_add, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      simp only [costEval_tensor, ResourcePool.weightedCount_add, leftIH, rightIH]
  | inverse body bodyIH => exact bodyIH
  | controlled _ body bodyIH => exact bodyIH
  | iterate count body bodyIH =>
      simp only [costEval_iterate, ResourcePool.weightedCount_nsmul, Nat.nsmul_eq_mul, bodyIH]
  | indexedProduct _ _ start step startIH stepIH =>
      simp only [costEval_indexedProduct, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_sum, startIH]
      congr 1
      exact Finset.sum_congr rfl (fun index _ => stepIH index)

/-- An independent coordinatewise pool budget bounds the actual critical path for every duration. -/
theorem depthEval_le_weightedCount_of_eventPool_le {model : ExecutionModel}
    (assign : Resource.Event model → Nat) (expression : DepthExpr (Resource.Event model))
    (budget : ResourcePool model)
    (bounded : costEval (fun event => ResourcePool.singleton event) expression ≤ budget) :
    depthEval assign expression ≤ ResourcePool.weightedCount assign budget :=
  (depthEval_le_costEval assign expression).trans
    ((costEval_eq_weightedCount assign expression).trans_le
      (ResourcePool.weightedCount_mono assign bounded))

end QuantumAlg.DepthExpr
