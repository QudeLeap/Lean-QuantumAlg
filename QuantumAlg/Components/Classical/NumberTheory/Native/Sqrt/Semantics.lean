/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.BodySemantics

/-!
# Complete native square-root execution through its actual lexical scopes

Each scope applies the existing workspace interpreter equation, retaining
all incoming quantum-reference blocks. The complete store map enters the
six real scratch heads, runs the actual body and releases exactly those
heads. Its output read is the original word's natural square root, with no
caller initialization or nonaliasing premise and with width zero included.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
    {environment : model.Environment} {ctx : RuntimeCtx model.kind} {width : Nat}

-- Package the existing complete interpreter equation so each scope can be
-- composed without repeatedly expanding all nested path instances.
private def StepLaw {current : RuntimeCtx model.kind} (program : Circuit model current current)
    (update : Store current → Store current × program.Path) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State current Reference (model.HiddenState × History)),
    program.execute environment Reference state = state.mapClassical (fun entry =>
      ((update entry.1).1, (entry.2.1, (entry.2.2, (update entry.1).2))))

private def scopeUpdate (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (program : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × program.Path)
    (store : Store ctx) :
    Store ctx × program.Path :=
  let next := update (store.pushWorkspace key shape fresh)
  (Store.popWorkspace key shape fresh next.1, next.2)

private lemma scopeEquation (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (program : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (Circuit.workspace ctx key shape fresh program)
      (scopeUpdate key shape fresh program update) := by
  intro Reference History historyFinite state
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) key shape fresh program
    (fun before => let actual := update before.1; ((actual.1, before.2), actual.2))
    (fun reference _history _ initial => law reference initial) Reference state).trans ?_
  congr 1

private def scoped5 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (squareContext ctx width) (squareContext ctx width) :=
  Circuit.workspace (squareContext ctx width) (squareContext ctx width).canonicalFreshKey
    .bit (squareContext ctx width).canonicalFreshKey_fresh program

private def update5 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (squareContext ctx width)) :
    Store (squareContext ctx width) × program.Path :=
  let next := update (store.pushWorkspace (squareContext ctx width).canonicalFreshKey
    .bit (squareContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation5 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (scoped5 (ctx := ctx) width program) (update5 (ctx :=
      ctx) width program update) := by
  exact scopeEquation (squareContext ctx width).canonicalFreshKey
    .bit (squareContext ctx width).canonicalFreshKey_fresh
    program update law

private def scoped4 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (candidateContext ctx width) (candidateContext ctx width) :=
  Circuit.workspace (candidateContext ctx width) (candidateContext ctx width).canonicalFreshKey
    (.unsignedWord (width + width)) (candidateContext ctx width).canonicalFreshKey_fresh
    (scoped5 (ctx := ctx) width program)

private def update4 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (candidateContext ctx width)) :
    Store (candidateContext ctx width) × program.Path :=
  let next := (update5 (ctx := ctx) width program update)
    (store.pushWorkspace (candidateContext ctx width).canonicalFreshKey
    (.unsignedWord (width + width)) (candidateContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation4 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (scoped4 (ctx := ctx) width program) (update4 (ctx :=
      ctx) width program update) := by
  exact scopeEquation (candidateContext ctx width).canonicalFreshKey
    (.unsignedWord (width + width)) (candidateContext ctx width).canonicalFreshKey_fresh
    (scoped5 (ctx := ctx) width program) (update5 (ctx := ctx) width program update)
    (equation5 (ctx := ctx) width program update law)

private def scoped3 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (halfContext ctx width) (halfContext ctx width) :=
  Circuit.workspace (halfContext ctx width) (halfContext ctx width).canonicalFreshKey
    (.unsignedWord width) (halfContext ctx width).canonicalFreshKey_fresh
    (scoped4 (ctx := ctx) width program)

private def update3 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (halfContext ctx width)) :
    Store (halfContext ctx width) × program.Path :=
  let next := (update4 (ctx := ctx) width program update)
    (store.pushWorkspace (halfContext ctx width).canonicalFreshKey
    (.unsignedWord width) (halfContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation3 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (scoped3 (ctx := ctx) width program) (update3 (ctx :=
      ctx) width program update) := by
  exact scopeEquation (halfContext ctx width).canonicalFreshKey
    (.unsignedWord width) (halfContext ctx width).canonicalFreshKey_fresh
    (scoped4 (ctx := ctx) width program) (update4 (ctx := ctx) width program update)
    (equation4 (ctx := ctx) width program update law)

private def scoped2 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (rootContext ctx width) (rootContext ctx width) :=
  Circuit.workspace (rootContext ctx width) (rootContext ctx width).canonicalFreshKey
    (.unsignedWord width) (rootContext ctx width).canonicalFreshKey_fresh
    (scoped3 (ctx := ctx) width program)

private def update2 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (rootContext ctx width)) :
    Store (rootContext ctx width) × program.Path :=
  let next := (update3 (ctx := ctx) width program update)
    (store.pushWorkspace (rootContext ctx width).canonicalFreshKey
    (.unsignedWord width) (rootContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation2 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (scoped2 (ctx := ctx) width program) (update2 (ctx :=
      ctx) width program update) := by
  exact scopeEquation (rootContext ctx width).canonicalFreshKey
    (.unsignedWord width) (rootContext ctx width).canonicalFreshKey_fresh
    (scoped3 (ctx := ctx) width program) (update3 (ctx := ctx) width program update)
    (equation3 (ctx := ctx) width program update law)

private def scoped1 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width)) :
    Circuit model (wideContext ctx width) (wideContext ctx width) :=
  Circuit.workspace (wideContext ctx width) (wideContext ctx width).canonicalFreshKey
    (.unsignedWord width) (wideContext ctx width).canonicalFreshKey_fresh
    (scoped2 (ctx := ctx) width program)

private def update1 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (wideContext ctx width)) :
    Store (wideContext ctx width) × program.Path :=
  let next := (update2 (ctx := ctx) width program update)
    (store.pushWorkspace (wideContext ctx width).canonicalFreshKey
    (.unsignedWord width) (wideContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh next.1, next.2)

private lemma equation1 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (scoped1 (ctx := ctx) width program) (update1 (ctx :=
      ctx) width program update) := by
  exact scopeEquation (wideContext ctx width).canonicalFreshKey
    (.unsignedWord width) (wideContext ctx width).canonicalFreshKey_fresh
    (scoped2 (ctx := ctx) width program) (update2 (ctx := ctx) width program update)
    (equation2 (ctx := ctx) width program update law)

private def scoped0 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width)) :
    Circuit model ctx ctx :=
  Circuit.workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh
    (scoped1 (ctx := ctx) width program)

private def update0 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store ctx) :
    Store ctx × program.Path :=
  let next := (update1 (ctx := ctx) width program update)
    (store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh next.1, next.2)

private lemma equation0 (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (law : StepLaw (environment := environment) program update) :
    StepLaw (environment := environment) (scoped0 (ctx := ctx) width program) (update0 (ctx :=
      ctx) width program update) := by
  exact scopeEquation ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh
    (scoped1 (ctx := ctx) width program) (update1 (ctx := ctx) width program update)
    (equation1 (ctx := ctx) width program update law)

private def push5 (width : Nat) (store : Store (squareContext ctx width)) :
    Store (context ctx width) :=
  store.pushWorkspace (squareContext ctx width).canonicalFreshKey
    .bit (squareContext ctx width).canonicalFreshKey_fresh

private def pop5 (width : Nat) (store : Store (context ctx width)) :
    Store (squareContext ctx width) :=
  Store.popWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh store

private lemma update5_store (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (squareContext ctx width)) :
    update5 (ctx := ctx) width program update store =
      (pop5 (ctx := ctx) width (update (push5 (ctx := ctx) width store)).1,
        (update (push5 (ctx := ctx) width store)).2) := rfl

private def push4 (width : Nat) (store : Store (candidateContext ctx width)) :
    Store (context ctx width) :=
  push5 (ctx := ctx) width (store.pushWorkspace (candidateContext ctx width).canonicalFreshKey
    (.unsignedWord (width + width)) (candidateContext ctx width).canonicalFreshKey_fresh)

private def pop4 (width : Nat) (store : Store (context ctx width)) :
    Store (candidateContext ctx width) :=
  Store.popWorkspace (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh (pop5 (ctx := ctx) width store)

private lemma update4_store (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (candidateContext ctx width)) :
    update4 (ctx := ctx) width program update store =
      (pop4 (ctx := ctx) width (update (push4 (ctx := ctx) width store)).1,
        (update (push4 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (squareContext ctx width) × program.Path =>
    (Store.popWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh next.1, next.2))
    (update5_store (ctx := ctx) width program update
      (store.pushWorkspace (candidateContext ctx width).canonicalFreshKey
        (.unsignedWord (width + width)) (candidateContext ctx width).canonicalFreshKey_fresh))

private def push3 (width : Nat) (store : Store (halfContext ctx width)) :
    Store (context ctx width) :=
  push4 (ctx := ctx) width (store.pushWorkspace (halfContext ctx width).canonicalFreshKey
    (.unsignedWord width) (halfContext ctx width).canonicalFreshKey_fresh)

private def pop3 (width : Nat) (store : Store (context ctx width)) :
    Store (halfContext ctx width) :=
  Store.popWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh (pop4 (ctx := ctx) width store)

private lemma update3_store (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (halfContext ctx width)) :
    update3 (ctx := ctx) width program update store =
      (pop3 (ctx := ctx) width (update (push3 (ctx := ctx) width store)).1,
        (update (push3 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (candidateContext ctx width) × program.Path =>
    (Store.popWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh next.1, next.2))
    (update4_store (ctx := ctx) width program update
      (store.pushWorkspace (halfContext ctx width).canonicalFreshKey
        (.unsignedWord width) (halfContext ctx width).canonicalFreshKey_fresh))

private def push2 (width : Nat) (store : Store (rootContext ctx width)) :
    Store (context ctx width) :=
  push3 (ctx := ctx) width (store.pushWorkspace (rootContext ctx width).canonicalFreshKey
    (.unsignedWord width) (rootContext ctx width).canonicalFreshKey_fresh)

private def pop2 (width : Nat) (store : Store (context ctx width)) :
    Store (rootContext ctx width) :=
  Store.popWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh (pop3 (ctx := ctx) width store)

private lemma update2_store (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (rootContext ctx width)) :
    update2 (ctx := ctx) width program update store =
      (pop2 (ctx := ctx) width (update (push2 (ctx := ctx) width store)).1,
        (update (push2 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (halfContext ctx width) × program.Path =>
    (Store.popWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh next.1, next.2))
    (update3_store (ctx := ctx) width program update
      (store.pushWorkspace (rootContext ctx width).canonicalFreshKey
        (.unsignedWord width) (rootContext ctx width).canonicalFreshKey_fresh))

private def push1 (width : Nat) (store : Store (wideContext ctx width)) :
    Store (context ctx width) :=
  push2 (ctx := ctx) width (store.pushWorkspace (wideContext ctx width).canonicalFreshKey
    (.unsignedWord width) (wideContext ctx width).canonicalFreshKey_fresh)

private def pop1 (width : Nat) (store : Store (context ctx width)) :
    Store (wideContext ctx width) :=
  Store.popWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh (pop2 (ctx := ctx) width store)

private lemma update1_store (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store (wideContext ctx width)) :
    update1 (ctx := ctx) width program update store =
      (pop1 (ctx := ctx) width (update (push1 (ctx := ctx) width store)).1,
        (update (push1 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (rootContext ctx width) × program.Path =>
    (Store.popWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh next.1, next.2))
    (update2_store (ctx := ctx) width program update
      (store.pushWorkspace (wideContext ctx width).canonicalFreshKey
        (.unsignedWord width) (wideContext ctx width).canonicalFreshKey_fresh))

private def push0 (width : Nat) (store : Store ctx) :
    Store (context ctx width) :=
  push1 (ctx := ctx) width (store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh)

private def pop0 (width : Nat) (store : Store (context ctx width)) :
    Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh (pop1 (ctx := ctx) width store)

private lemma update0_store (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store ctx) :
    update0 (ctx := ctx) width program update store =
      (pop0 (ctx := ctx) width (update (push0 (ctx := ctx) width store)).1,
        (update (push0 (ctx := ctx) width store)).2) := by
  exact congrArg (fun next : Store (wideContext ctx width) × program.Path =>
    (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh next.1, next.2))
    (update1_store (ctx := ctx) width program update
      (store.pushWorkspace ctx.canonicalFreshKey
        (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh))

private lemma push0_layout (width : Nat) (store : Store ctx) :
    push0 (ctx := ctx) width store = pushStore width store := rfl

private lemma pop0_layout (width : Nat) (store : Store (context ctx width)) :
    pop0 (ctx := ctx) width store = popStore width store := rfl

private lemma scoped_update_eq (width : Nat)
    (program : Circuit model (context ctx width) (context ctx width))
    (update : Store (context ctx width) → Store (context ctx width) × program.Path)
    (store : Store ctx) :
    update0 (ctx := ctx) width program update store =
      (popStore width (update (pushStore width store)).1,
        (update (pushStore width store)).2) := by
  simpa only [push0_layout, pop0_layout] using update0_store width program update store

variable [BitWord.Selected model]

/-- Actual complete entry, body execution and reverse release with the real body path. -/
def intoStep (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into (model := model) input output).Path :=
  let final := bodyStep (model := model) input output (pushStore width store)
  (popStore width final.1, final.2)

/-- The native square-root routine retains every complete quantum-reference block. -/
lemma nativeSqrt_into_execute (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) input output).execute environment
      Reference state = state.mapClassical (fun entry =>
      ((intoStep (model := model) input output entry.1).1,
        (entry.2.1, (entry.2.2, (intoStep (model := model) input output entry.1).2)))) := by
  have bodyLaw : StepLaw (environment := environment) (body (model := model) input output)
      (bodyStep (model := model) input output) := nativeSqrt_body_execute input output
  have scopedLaw := equation0 (ctx := ctx) width (body (model := model) input output)
    (bodyStep (model := model) input output) bodyLaw
  refine (scopedLaw Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
    (D := Store ctx × (model.HiddenState × (History × (into (model := model) input output).Path)))
  funext entry
  exact congrArg (fun final : Store ctx × (body (model := model) input output).Path =>
    (final.1, (entry.2.1, (entry.2.2, final.2))))
    (scoped_update_eq width (body (model := model) input output)
      (bodyStep (model := model) input output) entry.1)

/-- The final caller cell holds the exact square root of its original input at every width. -/
lemma nativeSqrt_into_read_output (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((intoStep (model := model) input output store).1.read (.storage output.toCStorageRef)).toNat =
      Nat.sqrt (store.read input).toNat := by
  have exited := nativeSqrt_pop_read (.storage output.toCStorageRef) width
    (bodyStep (model := model) input output (pushStore width store)).1
  rw [← nativeSqrt_underWrite_read output width] at exited
  exact (congrArg CShape.Value.toNat exited).trans
    (nativeSqrt_body_read_output (model := model) input output store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
