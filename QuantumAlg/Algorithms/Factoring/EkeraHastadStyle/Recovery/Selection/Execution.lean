/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Selection.Scope
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete native execution through the four selector cells

Each equation applies the existing single-workspace interpreter law to the
actual allocation constructor. Intermediate context and path types remain
explicit. The resulting update consists of the existing four real pushes,
the proved inner execution, and the same four reverse pops. Every incoming
quantum-reference block and the actual chronological path are preserved.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.SelectionLayout

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

private def StepLaw {current : RuntimeCtx model.kind} (inner : Circuit model current current)
    (update : Store current → Store current × inner.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State current Reference (model.HiddenState × History)),
    inner.execute environment Reference state = state.mapClassical (fun entry =>
      ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2))))

private lemma scopeEquation (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × inner.Path)
    (law : StepLaw (environment := environment) inner update) :
    StepLaw (environment := environment) (Circuit.workspace ctx key shape fresh inner)
      (fun store =>
        let next := update (store.pushWorkspace key shape fresh)
        (Store.popWorkspace key shape fresh next.1, next.2)) := by
  intro Reference History historyFinite state
  refine (Circuit.execute_workspace_mapClassical (environment := environment) key shape fresh inner
    (fun before => let actual := update before.1; ((actual.1, before.2), actual.2))
    (fun reference _history _ initial => law reference initial) Reference state).trans ?_
  congr 1

private def scoped3 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (availableCtx ctx width) (availableCtx ctx width) :=
  Circuit.workspace (availableCtx ctx width) (availableCtx ctx width).canonicalFreshKey
    .bit
    (availableCtx ctx width).canonicalFreshKey_fresh inner

private def update3 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (availableCtx ctx width)) : Store (availableCtx ctx width) × inner.Path :=
  let next := update
    (store.pushWorkspace (availableCtx ctx width).canonicalFreshKey
      .bit (availableCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit
    (availableCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation3 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw (environment := environment) inner update) :
    StepLaw (environment := environment) (scoped3 (ctx := ctx) width inner) (update3 (ctx := ctx)
      width inner update) := by
  exact scopeEquation (availableCtx ctx width).canonicalFreshKey
    .bit
    (availableCtx ctx width).canonicalFreshKey_fresh inner
    update law

private def scoped2 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (selectedCtx ctx width) (selectedCtx ctx width) :=
  Circuit.workspace (selectedCtx ctx width) (selectedCtx ctx width).canonicalFreshKey
    .bit
    (selectedCtx ctx width).canonicalFreshKey_fresh (scoped3 (ctx := ctx) width inner)

private def update2 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (selectedCtx ctx width)) : Store (selectedCtx ctx width) × inner.Path :=
  let next := (update3 (ctx := ctx) width inner update)
    (store.pushWorkspace (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit
    (selectedCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation2 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw (environment := environment) inner update) :
    StepLaw (environment := environment) (scoped2 (ctx := ctx) width inner) (update2 (ctx := ctx)
      width inner update) := by
  exact scopeEquation (selectedCtx ctx width).canonicalFreshKey
    .bit
    (selectedCtx ctx width).canonicalFreshKey_fresh (scoped3 (ctx := ctx) width inner)
    (update3 (ctx := ctx) width inner update) (equation3 (ctx := ctx) width inner update law)

private def scoped1 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (acceptedCtx ctx) (acceptedCtx ctx) :=
  Circuit.workspace (acceptedCtx ctx) (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width)
    (acceptedCtx ctx).canonicalFreshKey_fresh (scoped2 (ctx := ctx) width inner)

private def update1 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (acceptedCtx ctx)) : Store (acceptedCtx ctx) × inner.Path :=
  let next := (update2 (ctx := ctx) width inner update)
    (store.pushWorkspace (acceptedCtx ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh)
  (Store.popWorkspace (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width)
    (acceptedCtx ctx).canonicalFreshKey_fresh next.1, next.2)

private lemma equation1 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw (environment := environment) inner update) :
    StepLaw (environment := environment) (scoped1 (ctx := ctx) width inner) (update1 (ctx := ctx)
      width inner update) := by
  exact scopeEquation (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width)
    (acceptedCtx ctx).canonicalFreshKey_fresh (scoped2 (ctx := ctx) width inner)
    (update2 (ctx := ctx) width inner update) (equation2 (ctx := ctx) width inner update law)

private def scoped0 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) :
    Circuit model ctx ctx :=
  Circuit.workspace ctx ctx.canonicalFreshKey
    .bit
    ctx.canonicalFreshKey_fresh (scoped1 (ctx := ctx) width inner)

private def update0 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) : Store ctx × inner.Path :=
  let next := (update1 (ctx := ctx) width inner update)
    (store.pushWorkspace ctx.canonicalFreshKey
      .bit ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey
    .bit
    ctx.canonicalFreshKey_fresh next.1, next.2)

private lemma equation0 (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw (environment := environment) inner update) :
    StepLaw (environment := environment) (scoped0 (ctx := ctx) width inner) (update0 (ctx := ctx)
      width inner update) := by
  exact scopeEquation ctx.canonicalFreshKey
    .bit
    ctx.canonicalFreshKey_fresh (scoped1 (ctx := ctx) width inner)
    (update1 (ctx := ctx) width inner update) (equation1 (ctx := ctx) width inner update law)

/-- Four actual allocations and reverse releases retain exactly the true inner path. -/
def scopeStep (width : Nat) (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) : Store ctx × (scopes ctx width inner).Path :=
  update0 width inner update store

/-- The final store is the existing entry, actual inner update and existing reverse release. -/
lemma nativeRecovery_selectionScopeStep_store (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) :
    (scopeStep width inner update store).1 = popStore width (update (pushStore width store)).1 :=
  rfl

/-- The actual scoped circuit transports the complete proved inner execution equation. -/
lemma nativeRecovery_selectionScopes_execute (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx width) Reference (model.HiddenState × History)),
      inner.execute environment Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scopes ctx width inner).execute environment Reference state = state.mapClassical (fun entry =>
      ((scopeStep width inner update entry.1).1,
        (entry.2.1, (entry.2.2, (scopeStep width inner update entry.1).2)))) :=
  equation0 width inner update law Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.SelectionLayout
