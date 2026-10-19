/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Bank.Parallel.Layout
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Layout
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual parent scopes for all simultaneous reset outcomes

The parent enters one real finite-two workspace scope per bank wire before
calling its body, then removes all and only those scratch entries. No shape
is treated as several independently writable cells. Width zero introduces
no workspace and executes the supplied empty-bank body directly.
-/

namespace QuantumAlg.ZReset.BankParallel.Workspace

variable {model : ExecutionModel}

/-- Enter every scalar scratch scope before executing the supplied complete body. -/
def scope (ctx : RuntimeCtx model.kind) : (count : Nat) →
    Circuit model (context ctx count) (context ctx count) → Circuit model ctx ctx
  | 0, body => body
  | count + 1, body =>
      scope ctx count (Circuit.workspace (context ctx count)
        (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body)

/-- Lexical entry and exit contribute no artificial execution history. -/
def pathEquiv (ctx : RuntimeCtx model.kind) : (count : Nat) →
    (body : Circuit model (context ctx count) (context ctx count)) →
      (scope ctx count body).Path ≃ body.Path
  | 0, _ => Equiv.refl _
  | count + 1, body =>
      pathEquiv ctx count (Circuit.workspace (context ctx count)
        (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body)

/-- Parent allocation leaves the body's complete event trace unchanged. -/
lemma scope_eventTrace (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (path : (scope ctx count body).Path) :
    (scope ctx count body).eventTrace path = body.eventTrace (pathEquiv ctx count body path) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih _ path

/-- The literal event pool is unchanged by entering and leaving the parent scratch scopes. -/
lemma scope_resourcePool (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (path : (scope ctx count body).Path) :
    (scope ctx count body).resourcePool path =
      body.resourcePool (pathEquiv ctx count body path) := by
  unfold Circuit.resourcePool
  rw [scope_eventTrace]

/-- Parent allocation leaves the actual dependency expression unchanged. -/
lemma scope_depth (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (duration : Resource.Event model → Nat) (path : (scope ctx count body).Path) :
    (scope ctx count body).depth duration path =
      body.depth duration (pathEquiv ctx count body path) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih _ path

/-- Every intermediate parent scope is below the actual body resident peak. -/
lemma scope_peakResidentSpace_eq_body (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (path : (scope ctx count body).Path) :
    (scope ctx count body).peakResidentSpace path =
      body.peakResidentSpace (pathEquiv ctx count body path) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let allocatedBody := Circuit.workspace (context ctx count)
        (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body
      refine (ih allocatedBody path).trans ?_
      refine (Circuit.peakResidentSpace_workspace
        (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body
        (pathEquiv ctx count allocatedBody path)).trans ?_
      apply SpacePool.max_eq_right
      have boundary := Circuit.input_residentSpace_le_peak body
        (pathEquiv ctx count allocatedBody path)
      have earlier : (context ctx count).residentSpace ≤
          (context ctx (count + 1)).residentSpace := by
        rw [context, RuntimeCtx.residentSpace_addWorkspace]
        exact le_add_of_nonneg_left zero_le
      exact earlier.trans boundary

/-- Every intermediate parent scope is below the actual body auxiliary peak. -/
lemma scope_peakAuxiliarySpace_eq_body (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (path : (scope ctx count body).Path) :
    (scope ctx count body).peakAuxiliarySpace path =
      body.peakAuxiliarySpace (pathEquiv ctx count body path) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let allocatedBody := Circuit.workspace (context ctx count)
        (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body
      refine (ih allocatedBody path).trans ?_
      refine (Circuit.peakAuxiliarySpace_workspace
        (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body
        (pathEquiv ctx count allocatedBody path)).trans ?_
      apply SpacePool.max_eq_right
      have boundary := Circuit.input_auxiliarySpace_le_peak body
        (pathEquiv ctx count allocatedBody path)
      have earlier : (context ctx count).auxiliarySpace ≤
          (context ctx (count + 1)).auxiliarySpace := by
        rw [context, RuntimeCtx.auxiliarySpace_addWorkspace]
        exact le_add_of_nonneg_left zero_le
      exact earlier.trans boundary

/-- A fixed-context body reaches exactly the full parent-allocated resident capacity. -/
lemma scope_peakResidentSpace (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (bodyPeak : ∀ path, body.peakResidentSpace path = (context ctx count).residentSpace)
    (path : (scope ctx count body).Path) :
    (scope ctx count body).peakResidentSpace path =
      count • SpacePool.ofShape (.finite 2) + ctx.residentSpace := by
  rw [scope_peakResidentSpace_eq_body, bodyPeak, context_residentSpace]

/-- The same exact scalar cells contribute to the actual auxiliary peak. -/
lemma scope_peakAuxiliarySpace (ctx : RuntimeCtx model.kind) (count : Nat)
    (body : Circuit model (context ctx count) (context ctx count))
    (bodyPeak : ∀ path, body.peakAuxiliarySpace path = (context ctx count).auxiliarySpace)
    (path : (scope ctx count body).Path) :
    (scope ctx count body).peakAuxiliarySpace path =
      count • SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace := by
  rw [scope_peakAuxiliarySpace_eq_body, bodyPeak, context_auxiliarySpace]

end QuantumAlg.ZReset.BankParallel.Workspace
