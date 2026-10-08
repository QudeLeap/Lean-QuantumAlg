/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Unit event cost is the cardinality of the same expression's event pool

Both sides interpret one syntactic expression. The equality concerns total
event occurrences, including every tensor branch; it does not identify a
parallel critical path with the total cost. A scheduling theorem may use
this bridge after proving that shared controls serialize those occurrences.
-/

namespace QuantumAlg.DepthExpr

/-- Unit total cost counts exactly the events obtained from the same expression. -/
theorem unitCost_eq_eventPool_card {model : ExecutionModel}
    (expression : DepthExpr (Resource.Event model)) :
    DepthExpr.costEval (fun _ => (1 : Nat)) expression =
      (DepthExpr.costEval (fun event => ResourcePool.singleton event) expression).card := by
  induction expression with
  | id => rfl
  | atom event => simp [DepthExpr.costEval, ResourcePool.singleton]
  | seq left right leftIH rightIH =>
      simp only [DepthExpr.costEval_seq, Multiset.card_add, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      simp only [DepthExpr.costEval_tensor, Multiset.card_add, leftIH, rightIH]
  | inverse body bodyIH => exact bodyIH
  | controlled _ body bodyIH => exact bodyIH
  | iterate count body bodyIH =>
      simp only [DepthExpr.costEval_iterate, Multiset.card_nsmul,
        Nat.nsmul_eq_mul, bodyIH]
  | indexedProduct _ _ start step startIH stepIH =>
      simp only [DepthExpr.costEval_indexedProduct, Multiset.card_add,
        Multiset.card_sum, startIH]
      congr 1
      exact Finset.sum_congr rfl (fun index _ => stepIH index)

end QuantumAlg.DepthExpr
