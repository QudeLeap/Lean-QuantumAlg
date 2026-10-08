/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Layout.Store
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Exact actual execution through the five checker scopes

The real checker allocation and release order encloses precisely the supplied
actual inner circuit. Each of the five equations applies the existing native
workspace interpreter law, keeping the inner path type fixed while composing.
The resulting update is the same five real pushes, inner update and reverse
pops, with all original quantum-reference blocks retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

private def StepLaw {current : RuntimeCtx model.kind} (inner : Circuit model current current)
    (update : Store current → Store current × inner.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State current Reference (model.HiddenState × History)),
    inner.execute Reference state = state.mapClassical (fun entry =>
      ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2))))

private def scopeUpdate (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × inner.Path)
    (store : Store ctx) : Store ctx × inner.Path :=
  let next := update (store.pushWorkspace key shape fresh)
  (Store.popWorkspace key shape fresh next.1, next.2)

private theorem scopeEquation (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (Circuit.workspace ctx key shape fresh inner)
      (scopeUpdate key shape fresh inner update) := by
  intro Reference History historyFinite state
  refine (Circuit.execute_workspace_mapClassical key shape fresh inner
    (fun before => let actual := update before.1; ((actual.1, before.2), actual.2))
    (fun reference _history _ initial => law reference initial) Reference state).trans ?_
  congr 1

private def scoped4 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (firstCtx ctx width)
      (firstCtx ctx width) :=
  Circuit.workspace (firstCtx ctx width) (firstCtx ctx width).canonicalFreshKey .bit
    (firstCtx ctx width).canonicalFreshKey_fresh inner

private def update4 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (firstCtx ctx width)) : Store (firstCtx ctx width) × inner.Path :=
  let next := update (store.pushWorkspace (firstCtx ctx width).canonicalFreshKey
    .bit (firstCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (firstCtx ctx width).canonicalFreshKey .bit
    (firstCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation4 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped4 (ctx := ctx) width inner) (update4 (ctx := ctx) width inner update) :=
  scopeEquation (firstCtx ctx width).canonicalFreshKey .bit
    (firstCtx ctx width).canonicalFreshKey_fresh
    inner update law

private def scoped3 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (dividesCtx ctx width)
      (dividesCtx ctx width) :=
  Circuit.workspace (dividesCtx ctx width) (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh (scoped4 (ctx := ctx) width inner)

private def update3 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (dividesCtx ctx width)) : Store (dividesCtx ctx width) × inner.Path :=
  let next := update4 (ctx := ctx) width inner update
    (store.pushWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation3 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped3 (ctx := ctx) width inner) (update3 (ctx := ctx) width inner update) :=
  scopeEquation (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh
    (scoped4 (ctx := ctx) width inner) (update4 (ctx := ctx) width inner update)
    (equation4 (ctx := ctx) width inner update law)

private def scoped2 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (upperCtx ctx width)
      (upperCtx ctx width) :=
  Circuit.workspace (upperCtx ctx width) (upperCtx ctx width).canonicalFreshKey .bit
    (upperCtx ctx width).canonicalFreshKey_fresh (scoped3 (ctx := ctx) width inner)

private def update2 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (upperCtx ctx width)) : Store (upperCtx ctx width) × inner.Path :=
  let next := update3 (ctx := ctx) width inner update
    (store.pushWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (upperCtx ctx width).canonicalFreshKey .bit
    (upperCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation2 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped2 (ctx := ctx) width inner) (update2 (ctx := ctx) width inner update) :=
  scopeEquation (upperCtx ctx width).canonicalFreshKey .bit
    (upperCtx ctx width).canonicalFreshKey_fresh
    (scoped3 (ctx := ctx) width inner) (update3 (ctx := ctx) width inner update)
    (equation3 (ctx := ctx) width inner update law)

private def scoped1 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (zeroCtx ctx width)
      (zeroCtx ctx width) :=
  Circuit.workspace (zeroCtx ctx width) (zeroCtx ctx width).canonicalFreshKey .bit
    (zeroCtx ctx width).canonicalFreshKey_fresh (scoped2 (ctx := ctx) width inner)

private def update1 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (zeroCtx ctx width)) : Store (zeroCtx ctx width) × inner.Path :=
  let next := update2 (ctx := ctx) width inner update
    (store.pushWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
    (zeroCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation1 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped1 (ctx := ctx) width inner) (update1 (ctx := ctx) width inner update) :=
  scopeEquation (zeroCtx ctx width).canonicalFreshKey .bit
    (zeroCtx ctx width).canonicalFreshKey_fresh
    (scoped2 (ctx := ctx) width inner) (update2 (ctx := ctx) width inner update)
    (equation2 (ctx := ctx) width inner update law)

private def scoped0 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) : Circuit model ctx ctx :=
  Circuit.workspace ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scoped1 (ctx := ctx) width inner)

private def update0 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) : Store ctx × inner.Path :=
  let next := (update1 (ctx := ctx) width inner update) (store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh next.1, next.2)

private theorem equation0 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped0 (ctx := ctx) width inner) (update0 (ctx := ctx) width inner update) :=
  scopeEquation ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (scoped1 (ctx := ctx) width inner) (update1 (ctx := ctx) width inner update)
    (equation1 (ctx := ctx) width inner update law)

/-- The actual five scopes record the same inner path while returning to the original store type.
-/
def scopeStep (width : Nat) (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) : Store ctx × (scopes ctx width inner).Path :=
  update0 width inner update store

/-- The recorded final store is precisely actual entry, inner execution update and release. -/
theorem nativeQuadratic_checkScopeStep_store (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) :
    (scopeStep width inner update store).1 = popStore width (update (pushStore width store)).1 :=
      rfl

/-- Actual allocation and release transport the proved complete inner interpreter equation. -/
theorem nativeQuadratic_checkScopes_execute (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx width) Reference (model.HiddenState × History)),
      inner.execute Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scopes ctx width inner).execute Reference state = state.mapClassical (fun entry =>
      ((scopeStep width inner update entry.1).1,
        (entry.2.1, (entry.2.2, (scopeStep width inner update entry.1).2)))) :=
  equation0 width inner update law Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
