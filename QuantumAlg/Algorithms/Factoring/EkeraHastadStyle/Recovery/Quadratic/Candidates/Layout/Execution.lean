/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Layout.Store
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete native execution through the four candidate words

Each equation applies the existing single-workspace interpreter law to the
actual allocation constructor. Intermediate context and path types remain
explicit. The resulting update consists of the existing four real pushes,
the proved inner execution, and the same four reverse pops. Every incoming
quantum-reference block and the actual chronological path are preserved.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Layout

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private def StepLaw {current : RuntimeCtx kind} (inner : Circuit current current)
    (update : Store current → Store current × inner.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State current Reference History),
    inner.execute Reference state = state.mapClassical (fun entry =>
      ((update entry.1).1, (entry.2, (update entry.1).2)))

private def scoped3 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width)) :
    Circuit (firstCtx ctx width) (firstCtx ctx width) :=
  Circuit.workspace (firstCtx ctx width) (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (firstCtx ctx width).canonicalFreshKey_fresh inner

private def update3 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (firstCtx ctx width)) : Store (firstCtx ctx width) × inner.Path :=
  let next := update
    (store.pushWorkspace (firstCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (firstCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (firstCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation3 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped3 (ctx := ctx) width inner) (update3 (ctx := ctx) width inner update) := by
  intro Reference History historyFinite state
  exact Circuit.execute_workspace_mapClassical (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (firstCtx ctx width).canonicalFreshKey_fresh inner
    update law
    Reference state

private def scoped2 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width)) :
    Circuit (rootCtx ctx width) (rootCtx ctx width) :=
  Circuit.workspace (rootCtx ctx width) (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (rootCtx ctx width).canonicalFreshKey_fresh (scoped3 (ctx := ctx) width inner)

private def update2 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (rootCtx ctx width)) : Store (rootCtx ctx width) × inner.Path :=
  let next := (update3 (ctx := ctx) width inner update)
    (store.pushWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (rootCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation2 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped2 (ctx := ctx) width inner) (update2 (ctx := ctx) width inner update) := by
  intro Reference History historyFinite state
  exact Circuit.execute_workspace_mapClassical (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (rootCtx ctx width).canonicalFreshKey_fresh (scoped3 (ctx := ctx) width inner)
    (update3 (ctx := ctx) width inner update) (equation3 (ctx := ctx) width inner update law)
    Reference state

private def scoped1 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width)) :
    Circuit (centerCtx ctx width) (centerCtx ctx width) :=
  Circuit.workspace (centerCtx ctx width) (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (centerCtx ctx width).canonicalFreshKey_fresh (scoped2 (ctx := ctx) width inner)

private def update1 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store (centerCtx ctx width)) : Store (centerCtx ctx width) × inner.Path :=
  let next := (update2 (ctx := ctx) width inner update)
    (store.pushWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (centerCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private theorem equation1 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped1 (ctx := ctx) width inner) (update1 (ctx := ctx) width inner update) := by
  intro Reference History historyFinite state
  exact Circuit.execute_workspace_mapClassical (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (centerCtx ctx width).canonicalFreshKey_fresh (scoped2 (ctx := ctx) width inner)
    (update2 (ctx := ctx) width inner update) (equation2 (ctx := ctx) width inner update law)
    Reference state

private def scoped0 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width)) :
    Circuit ctx ctx :=
  Circuit.workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    ctx.canonicalFreshKey_fresh (scoped1 (ctx := ctx) width inner)

private def update0 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) : Store ctx × inner.Path :=
  let next := (update1 (ctx := ctx) width inner update)
    (store.pushWorkspace ctx.canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    ctx.canonicalFreshKey_fresh next.1, next.2)

private theorem equation0 (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : StepLaw inner update) :
    StepLaw (scoped0 (ctx := ctx) width inner) (update0 (ctx := ctx) width inner update) := by
  intro Reference History historyFinite state
  exact Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    ctx.canonicalFreshKey_fresh (scoped1 (ctx := ctx) width inner)
    (update1 (ctx := ctx) width inner update) (equation1 (ctx := ctx) width inner update law)
    Reference state

/-- Four actual allocations and reverse releases retain exactly the true inner path. -/
def scopeStep (width : Nat) (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) : Store ctx × (scopes ctx width inner).Path :=
  update0 width inner update store

/-- The final store is the existing entry, actual inner update and existing reverse release. -/
theorem nativeQuadratic_layoutScopeStep_store (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (store : Store ctx) :
    (scopeStep width inner update store).1 = popStore width (update (pushStore width store)).1 :=
  rfl

/-- The actual scoped circuit transports the complete proved inner execution equation. -/
theorem nativeQuadratic_layoutScopes_execute (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × inner.Path)
    (law : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx width) Reference History),
      inner.execute Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2, (update entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scopes ctx width inner).execute Reference state = state.mapClassical (fun entry =>
      ((scopeStep width inner update entry.1).1,
        (entry.2, (scopeStep width inner update entry.1).2))) :=
  equation0 width inner update law Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Layout
