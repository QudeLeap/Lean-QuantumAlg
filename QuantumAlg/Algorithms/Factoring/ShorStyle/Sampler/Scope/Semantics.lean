/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Exact execution through the sampler's eleven real workspace scopes

Each typed step below applies the established interpreter equation for one
actual allocation and release. Their composition uses the layout's literal
push and pop operations, so the final state has the original caller context
and keeps every complete quantum-reference block.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

-- This private predicate only packages the existing full interpreter equation.
-- Keeping it closed while composing scopes avoids expanding path instances at each layer.
private def ExecutesBy (environment : model.Environment) {ctx : RuntimeCtx model.kind}
    (code : Circuit model ctx ctx)
    (update : Store ctx → Store ctx × code.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)),
    code.execute environment Reference state = state.mapClassical (fun entry =>
      ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2))))

private def workspaceUpdate (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × body.Path) (store : Store ctx) :
    Store ctx × body.Path :=
  let next := update (store.pushWorkspace key shape fresh)
  (Store.popWorkspace key shape fresh next.1, next.2)

private lemma workspace_executesBy (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (Circuit.workspace ctx key shape fresh body)
      (workspaceUpdate key shape fresh body update) := by
  intro Reference History historyFinite state
  refine (Circuit.execute_workspace_mapClassical (environment := environment) key shape fresh body
    (fun entry =>
      let result := update entry.1
      ((result.1, entry.2), result.2))
    (fun reference history _ initial =>
      (bodyEquation reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def body10 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.availableCtx ctx width) (Layout.availableCtx ctx width) :=
  Circuit.workspace (Layout.availableCtx ctx width)
    (Layout.availableCtx ctx width).canonicalFreshKey
    .bit (Layout.availableCtx ctx width).canonicalFreshKey_fresh
    body

private def update10 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.availableCtx ctx width)) :
    Store (Layout.availableCtx ctx width) × body.Path :=
  let next := update (initial.pushWorkspace (Layout.availableCtx ctx width).canonicalFreshKey
    .bit (Layout.availableCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.availableCtx ctx width).canonicalFreshKey .bit
    (Layout.availableCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation10 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body10 (ctx := ctx) width body)
      (update10 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.availableCtx ctx width).canonicalFreshKey
    .bit (Layout.availableCtx ctx width).canonicalFreshKey_fresh
    body update
    bodyEquation

private def body9 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.selectedCtx ctx width) (Layout.selectedCtx ctx width) :=
  Circuit.workspace (Layout.selectedCtx ctx width) (Layout.selectedCtx ctx width).canonicalFreshKey
    .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh
    (body10 (ctx := ctx) width body)

private def update9 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.selectedCtx ctx width)) :
    Store (Layout.selectedCtx ctx width) × body.Path :=
  let next := (update10 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey
    .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey .bit
    (Layout.selectedCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation9 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body9 (ctx := ctx) width body)
      (update9 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.selectedCtx ctx width).canonicalFreshKey
    .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh
    (body10 (ctx := ctx) width body) (update10 (ctx := ctx) width body update)
    (equation10 (ctx := ctx) width body update bodyEquation)

private def body8 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.acceptedCtx ctx width) (Layout.acceptedCtx ctx width) :=
  Circuit.workspace (Layout.acceptedCtx ctx width) (Layout.acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh
    (body9 (ctx := ctx) width body)

private def update8 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.acceptedCtx ctx width)) :
    Store (Layout.acceptedCtx ctx width) × body.Path :=
  let next := (update9 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation8 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body8 (ctx := ctx) width body)
      (update8 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh
    (body9 (ctx := ctx) width body) (update9 (ctx := ctx) width body update)
    (equation9 (ctx := ctx) width body update bodyEquation)

private def body7 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.eligibleCtx ctx width) (Layout.eligibleCtx ctx width) :=
  Circuit.workspace (Layout.eligibleCtx ctx width) (Layout.eligibleCtx ctx width).canonicalFreshKey
    .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh
    (body8 (ctx := ctx) width body)

private def update7 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.eligibleCtx ctx width)) :
    Store (Layout.eligibleCtx ctx width) × body.Path :=
  let next := (update8 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey
    .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
    (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation7 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body7 (ctx := ctx) width body)
      (update7 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.eligibleCtx ctx width).canonicalFreshKey
    .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh
    (body8 (ctx := ctx) width body) (update8 (ctx := ctx) width body update)
    (equation8 (ctx := ctx) width body update bodyEquation)

private def body6 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.belowCtx ctx width) (Layout.belowCtx ctx width) :=
  Circuit.workspace (Layout.belowCtx ctx width) (Layout.belowCtx ctx width).canonicalFreshKey
    .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh
    (body7 (ctx := ctx) width body)

private def update6 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.belowCtx ctx width)) :
    Store (Layout.belowCtx ctx width) × body.Path :=
  let next := (update7 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.belowCtx ctx width).canonicalFreshKey
    .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.belowCtx ctx width).canonicalFreshKey .bit
    (Layout.belowCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation6 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body6 (ctx := ctx) width body)
      (update6 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.belowCtx ctx width).canonicalFreshKey
    .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh
    (body7 (ctx := ctx) width body) (update7 (ctx := ctx) width body update)
    (equation7 (ctx := ctx) width body update bodyEquation)

private def body5 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.positiveCtx ctx width) (Layout.positiveCtx ctx width) :=
  Circuit.workspace (Layout.positiveCtx ctx width) (Layout.positiveCtx ctx width).canonicalFreshKey
    .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh
    (body6 (ctx := ctx) width body)

private def update5 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.positiveCtx ctx width)) :
    Store (Layout.positiveCtx ctx width) × body.Path :=
  let next := (update6 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey
    .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey .bit
    (Layout.positiveCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation5 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body5 (ctx := ctx) width body)
      (update5 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.positiveCtx ctx width).canonicalFreshKey
    .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh
    (body6 (ctx := ctx) width body) (update6 (ctx := ctx) width body update)
    (equation6 (ctx := ctx) width body update bodyEquation)

private def body4 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.extendedCtx ctx width) (Layout.extendedCtx ctx width) :=
  Circuit.workspace (Layout.extendedCtx ctx width) (Layout.extendedCtx ctx width).canonicalFreshKey
    .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh
    (body5 (ctx := ctx) width body)

private def update4 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.extendedCtx ctx width)) :
    Store (Layout.extendedCtx ctx width) × body.Path :=
  let next := (update5 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey
    .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey .bit
    (Layout.extendedCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation4 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body4 (ctx := ctx) width body)
      (update4 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.extendedCtx ctx width).canonicalFreshKey
    .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh
    (body5 (ctx := ctx) width body) (update5 (ctx := ctx) width body update)
    (equation5 (ctx := ctx) width body update bodyEquation)

private def body3 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.candidateCtx ctx width) (Layout.candidateCtx ctx width) :=
  Circuit.workspace (Layout.candidateCtx ctx width)
    (Layout.candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh
    (body4 (ctx := ctx) width body)

private def update3 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.candidateCtx ctx width)) :
    Store (Layout.candidateCtx ctx width) × body.Path :=
  let next := (update4 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
    (Layout.candidateCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation3 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body3 (ctx := ctx) width body)
      (update3 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh
    (body4 (ctx := ctx) width body) (update4 (ctx := ctx) width body update)
    (equation4 (ctx := ctx) width body update bodyEquation)

private def body2 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.gcdCtx ctx width) (Layout.gcdCtx ctx width) :=
  Circuit.workspace (Layout.gcdCtx ctx width) (Layout.gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh
    (body3 (ctx := ctx) width body)

private def update2 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.gcdCtx ctx width)) :
    Store (Layout.gcdCtx ctx width) × body.Path :=
  let next := (update3 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (Layout.gcdCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation2 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body2 (ctx := ctx) width body)
      (update2 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh
    (body3 (ctx := ctx) width body) (update3 (ctx := ctx) width body update)
    (equation3 (ctx := ctx) width body update bodyEquation)

private def body1 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model (Layout.modulusCtx ctx width) (Layout.modulusCtx ctx width) :=
  Circuit.workspace (Layout.modulusCtx ctx width) (Layout.modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh
    (body2 (ctx := ctx) width body)

private def update1 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store (Layout.modulusCtx ctx width)) :
    Store (Layout.modulusCtx ctx width) × body.Path :=
  let next := (update2 (ctx := ctx) width body update)
    (initial.pushWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
    (Layout.modulusCtx ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation1 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body1 (ctx := ctx) width body)
      (update1 (ctx := ctx) width body update) := by
  exact workspace_executesBy (Layout.modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh
    (body2 (ctx := ctx) width body) (update2 (ctx := ctx) width body update)
    (equation2 (ctx := ctx) width body update bodyEquation)

private def body0 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width)) :
    Circuit model ctx ctx :=
  Circuit.workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (body1 (ctx := ctx) width body)

private def update0 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (initial : Store ctx) :
    Store ctx × body.Path :=
  let next := (update1 (ctx := ctx) width body update) (initial.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh next.1, next.2)

private lemma equation0 (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ExecutesBy environment body update) :
    ExecutesBy environment (body0 (ctx := ctx) width body)
      (update0 (ctx := ctx) width body update) := by
  exact workspace_executesBy ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (body1 (ctx := ctx) width body) (update1 (ctx := ctx) width body update)
    (equation1 (ctx := ctx) width body update bodyEquation)

-- The store-only chain is proved separately from full-state/path-instance elaboration.
private def push10 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.availableCtx ctx width)) :
    Store (Layout.context ctx width) :=
  store.pushWorkspace (Layout.availableCtx ctx width).canonicalFreshKey
    .bit (Layout.availableCtx ctx width).canonicalFreshKey_fresh

private def pop10 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.availableCtx ctx width) :=
  Store.popWorkspace (Layout.availableCtx ctx width).canonicalFreshKey .bit
    (Layout.availableCtx ctx width).canonicalFreshKey_fresh store

private lemma update10_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.availableCtx ctx width)) :
    update10 (ctx := ctx) width body update store =
      (pop10 (ctx := ctx) width (update (push10 (ctx := ctx) width store)).1,
        (update (push10 (ctx := ctx) width store)).2) := rfl

private def push9 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.selectedCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push10 (ctx := ctx) width (store.pushWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey
    .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh)

private def pop9 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.selectedCtx ctx width) :=
  Store.popWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey .bit
    (Layout.selectedCtx ctx width).canonicalFreshKey_fresh (pop10 (ctx := ctx) width store)

private lemma update9_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.selectedCtx ctx width)) :
    update9 (ctx := ctx) width body update store =
      (pop9 (ctx := ctx) width (update (push9 (ctx := ctx) width store)).1,
        (update (push9 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.availableCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey .bit
      (Layout.selectedCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update10_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey
          .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh))

private def push8 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.acceptedCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push9 (ctx := ctx) width (store.pushWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh)

private def pop8 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.acceptedCtx ctx width) :=
  Store.popWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh (pop9 (ctx := ctx) width store)

private lemma update8_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.acceptedCtx ctx width)) :
    update8 (ctx := ctx) width body update store =
      (pop8 (ctx := ctx) width (update (push8 (ctx := ctx) width store)).1,
        (update (push8 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.selectedCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update9_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey
          (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh))

private def push7 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.eligibleCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push8 (ctx := ctx) width (store.pushWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey
    .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh)

private def pop7 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.eligibleCtx ctx width) :=
  Store.popWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
    (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh (pop8 (ctx := ctx) width store)

private lemma update7_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.eligibleCtx ctx width)) :
    update7 (ctx := ctx) width body update store =
      (pop7 (ctx := ctx) width (update (push7 (ctx := ctx) width store)).1,
        (update (push7 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.acceptedCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
      (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update8_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey
          .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh))

private def push6 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.belowCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push7 (ctx := ctx) width (store.pushWorkspace (Layout.belowCtx ctx width).canonicalFreshKey
    .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh)

private def pop6 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.belowCtx ctx width) :=
  Store.popWorkspace (Layout.belowCtx ctx width).canonicalFreshKey .bit
    (Layout.belowCtx ctx width).canonicalFreshKey_fresh (pop7 (ctx := ctx) width store)

private lemma update6_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.belowCtx ctx width)) :
    update6 (ctx := ctx) width body update store =
      (pop6 (ctx := ctx) width (update (push6 (ctx := ctx) width store)).1,
        (update (push6 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.eligibleCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.belowCtx ctx width).canonicalFreshKey .bit
      (Layout.belowCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update7_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.belowCtx ctx width).canonicalFreshKey
          .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh))

private def push5 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.positiveCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push6 (ctx := ctx) width (store.pushWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey
    .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh)

private def pop5 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.positiveCtx ctx width) :=
  Store.popWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey .bit
    (Layout.positiveCtx ctx width).canonicalFreshKey_fresh (pop6 (ctx := ctx) width store)

private lemma update5_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.positiveCtx ctx width)) :
    update5 (ctx := ctx) width body update store =
      (pop5 (ctx := ctx) width (update (push5 (ctx := ctx) width store)).1,
        (update (push5 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.belowCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey .bit
      (Layout.positiveCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update6_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey
          .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh))

private def push4 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.extendedCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push5 (ctx := ctx) width (store.pushWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey
    .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh)

private def pop4 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.extendedCtx ctx width) :=
  Store.popWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey .bit
    (Layout.extendedCtx ctx width).canonicalFreshKey_fresh (pop5 (ctx := ctx) width store)

private lemma update4_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.extendedCtx ctx width)) :
    update4 (ctx := ctx) width body update store =
      (pop4 (ctx := ctx) width (update (push4 (ctx := ctx) width store)).1,
        (update (push4 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.positiveCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey .bit
      (Layout.extendedCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update5_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey
          .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh))

private def push3 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.candidateCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push4 (ctx := ctx) width (store.pushWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh)

private def pop3 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.candidateCtx ctx width) :=
  Store.popWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
    (Layout.candidateCtx ctx width).canonicalFreshKey_fresh (pop4 (ctx := ctx) width store)

private lemma update3_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.candidateCtx ctx width)) :
    update3 (ctx := ctx) width body update store =
      (pop3 (ctx := ctx) width (update (push3 (ctx := ctx) width store)).1,
        (update (push3 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.extendedCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
    (Layout.candidateCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update4_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
          (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh))

private def push2 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.gcdCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push3 (ctx := ctx) width (store.pushWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh)

private def pop2 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.gcdCtx ctx width) :=
  Store.popWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (Layout.gcdCtx ctx width).canonicalFreshKey_fresh (pop3 (ctx := ctx) width store)

private lemma update2_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.gcdCtx ctx width)) :
    update2 (ctx := ctx) width body update store =
      (pop2 (ctx := ctx) width (update (push2 (ctx := ctx) width store)).1,
        (update (push2 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.candidateCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.gcdCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update3_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey
          (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh))

private def push1 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.modulusCtx ctx width)) :
    Store (Layout.context ctx width) :=
  push2 (ctx := ctx) width (store.pushWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh)

private def pop1 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store (Layout.modulusCtx ctx width) :=
  Store.popWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
    (Layout.modulusCtx ctx width).canonicalFreshKey_fresh (pop2 (ctx := ctx) width store)

private lemma update1_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store (Layout.modulusCtx ctx width)) :
    update1 (ctx := ctx) width body update store =
      (pop1 (ctx := ctx) width (update (push1 (ctx := ctx) width store)).1,
        (update (push1 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.gcdCtx ctx width) × body.Path =>
    (Store.popWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (Layout.modulusCtx ctx width).canonicalFreshKey_fresh next.1, next.2))
      (update2_store (ctx := ctx) width body update
        (store.pushWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey
          (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh))

private def push0 {kind : ProblemKind} {ctx : RuntimeCtx kind} (width : Nat) (store : Store ctx) :
    Store (Layout.context ctx width) :=
  push1 (ctx := ctx) width (store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh)

private def pop0 {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (pop1 (ctx := ctx) width store)

private lemma update0_store (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store ctx) :
    update0 (ctx := ctx) width body update store =
      (pop0 (ctx := ctx) width (update (push0 (ctx := ctx) width store)).1,
        (update (push0 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (Layout.modulusCtx ctx width) × body.Path =>
    (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh next.1, next.2))
      (update1_store (ctx := ctx) width body update
        (store.pushWorkspace ctx.canonicalFreshKey
          (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh))

private lemma push0_layout {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store ctx) :
    push0 (ctx := ctx) width store = Layout.pushStore width store := rfl

private lemma pop0_layout {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (store : Store (Layout.context ctx width)) :
    pop0 (ctx := ctx) width store = Layout.popStore width store := rfl

private lemma update0_layout (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (store : Store ctx) :
    update0 (ctx := ctx) width body update store =
      (Layout.popStore width (update (Layout.pushStore width store)).1,
        (update (Layout.pushStore width store)).2) := by
  simpa only [push0_layout, pop0_layout] using update0_store (ctx := ctx) width body update store

/-- The eleven actual scopes compose a proved inner update on the complete caller state. -/
lemma samplerScopes_execute (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (update : Store (Layout.context ctx width) → Store (Layout.context ctx width) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (Layout.context ctx width) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scopes ctx width body).execute environment Reference state =
      state.mapClassical (fun entry =>
        (Layout.popStore width (update (Layout.pushStore width entry.1)).1,
          (entry.2.1, (entry.2.2, (update (Layout.pushStore width entry.1)).2)))) := by
  have bodyLaw : ExecutesBy environment (scopes ctx width body)
    (update0 (ctx := ctx) width body update) :=
    equation0 (ctx := ctx) width body update bodyEquation
  refine (bodyLaw Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  exact congrArg (fun next : Store ctx × body.Path =>
    (next.1, (entry.2.1, (entry.2.2, next.2))))
    (update0_layout (ctx := ctx) width body update entry.1)

variable [BitWord.Selected model]

/-- Actual scoped residue preparation executes its exact caller-store and instruction-path map. -/
lemma samplerProgram_execute (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (circuit (model := model) N sample output).execute environment Reference state =
      state.mapClassical (fun entry => ((step (model := model) N sample output entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) N sample output entry.1).2)))) := by
  refine (samplerScopes_execute (modulusBits N) (inner (model := model) N sample output)
    (innerStep (model := model) N sample output)
    (samplerInner_execute N sample output) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
