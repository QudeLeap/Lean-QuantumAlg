/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr
import Mathlib.Data.List.OfFn

/-!
# Exact resources of uniform-dimensional zero preparation

Every actual fresh system contributes its own dimension-tagged preparation
coordinate. Independent systems have parallel unit depth one when nonempty,
and zero when empty. The surrounding classical models remain arbitrary.
-/

namespace QuantumAlg.ZeroPreparation

variable (gates : GateModel) (oracles : OracleModel)
  {count : Nat} (layout : QuantumLayout count) (dimension : ℕ+)
  (uniform : ∀ index, (layout.wire index).dimension = dimension)
  (operations : ClassicalOpModel := .empty)
  (services : ClassicalOracleModel := .empty)

include uniform in
/-- Uniform dimensions retain one literal preparation occurrence per physical system. -/
public theorem zeroPreparation_uniform_trace :
    eventTrace gates oracles layout operations services =
      List.replicate count
        (Resource.Event.preparation (model := .quantum gates oracles operations services)
          dimension) := by
  simp only [eventTrace, uniform, List.ofFn_const]

include uniform in
/-- The complete native pool counts every prepared system, including a possible empty layout. -/
public theorem zeroPreparation_uniform_cost :
    eventCost gates oracles layout operations services =
      count • ResourcePool.singleton
        (model := .quantum gates oracles operations services) (.preparation dimension) := by
  rw [eventCost, zeroPreparation_uniform_trace gates oracles layout dimension uniform
      operations services,
    ResourcePool.ofList_replicate]
  rfl

private theorem parallel_replicate_unit_depth {Event : Type} (event : Event) (count : Nat) :
    DepthExpr.depthEval (fun _ => 1)
      ((List.replicate count event).foldr
        (fun item depth => DepthExpr.tensor (.atom item) depth) .id) =
      if count = 0 then 0 else 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.foldr_cons, DepthExpr.depthEval, ih,
        Nat.succ_ne_zero, ↓reduceIte]
      split <;> rfl

private theorem parallel_list_unit_depth {Event : Type} (events : List Event) :
    DepthExpr.depthEval (fun _ => 1)
      (events.foldr (fun event depth => DepthExpr.tensor (.atom event) depth) .id) =
      if events = [] then 0 else 1 := by
  induction events with
  | nil => rfl
  | cons event events induction =>
      simp only [List.foldr_cons, DepthExpr.depthEval_tensor,
        DepthExpr.depthEval_atom, induction]
      cases events <;> rfl

/-- Any nonempty mixed-dimensional fresh bank still prepares in one parallel layer. -/
public theorem zeroPreparation_unit_depth
    (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count)
    (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty) :
    DepthExpr.depthEval (fun _ => 1)
      (eventDepth gates oracles layout operations services) =
        if count = 0 then 0 else 1 := by
  rw [eventDepth, parallel_list_unit_depth]
  simp [eventTrace]

include uniform in
/-- Independent fresh preparations have exactly one nonempty unit-duration layer. -/
public theorem zeroPreparation_uniform_unit_depth :
    DepthExpr.depthEval (fun _ => 1) (eventDepth gates oracles layout operations services) =
      if count = 0 then 0 else 1 := by
  rw [eventDepth, zeroPreparation_uniform_trace gates oracles layout dimension uniform
    operations services]
  exact parallel_replicate_unit_depth _ count

end QuantumAlg.ZeroPreparation
