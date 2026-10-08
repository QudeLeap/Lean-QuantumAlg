/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.BodyExecution
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Complete execution through the seven actual factor-recovery scopes

Each private tail is the corresponding literal subtree of the already defined
factor scope. The existing workspace execution theorem derives its real push,
body execution and pop. The full record retains every actual selected path
and the complete Store-history block on the unchanged quantum-reference register.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {N : Nat}

private def part6 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model
  (positiveContext ctx N) (positiveContext ctx N) :=
  .workspace (positiveContext ctx N) (positiveContext ctx N).canonicalFreshKey (.unsignedWord
    (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh tail

private def update6 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store (positiveContext ctx N)) :
    Store (positiveContext ctx N) × tail.Path :=
  let selected := record (store.pushWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (positiveContext ctx N).canonicalFreshKey (.unsignedWord (modulusBits N))
    (positiveContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation6 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (positiveContext ctx N) Reference (model.HiddenState × History)) :
    (part6 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update6 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (positiveContext ctx N).canonicalFreshKey (.unsignedWord
    (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
    tail (fun entry =>
      let actual := record entry.1
      ((actual.1, entry.2), actual.2))
    equation Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part5 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model
  (activeContext ctx N) (activeContext ctx N) :=
  .workspace (activeContext ctx N) (activeContext ctx N).canonicalFreshKey .bit (activeContext ctx
    N).canonicalFreshKey_fresh (part6 tail)

private def update5 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store (activeContext ctx N)) :
    Store (activeContext ctx N) × tail.Path :=
  let selected := (update6 tail record) (store.pushWorkspace (activeContext ctx
    N).canonicalFreshKey .bit (activeContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (activeContext ctx N).canonicalFreshKey .bit (activeContext ctx
    N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation5 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (activeContext ctx N) Reference (model.HiddenState × History)) :
    (part5 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update5 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (activeContext ctx N).canonicalFreshKey .bit
    (activeContext ctx N).canonicalFreshKey_fresh
    (part6 tail) (fun entry =>
      let actual := (update6 tail record) entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation6 (model := model) (ctx := ctx) (N := N) tail record equation reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update5]
    rfl

private def part4 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model
  (zeroContext ctx N) (zeroContext ctx N) :=
  .workspace (zeroContext ctx N) (zeroContext ctx N).canonicalFreshKey .bit (zeroContext ctx
    N).canonicalFreshKey_fresh (part5 tail)

private def update4 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store (zeroContext ctx N)) :
    Store (zeroContext ctx N) × tail.Path :=
  let selected := (update5 tail record) (store.pushWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (zeroContext ctx N).canonicalFreshKey .bit (zeroContext ctx
    N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation4 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (zeroContext ctx N) Reference (model.HiddenState × History)) :
    (part4 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update4 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (zeroContext ctx N).canonicalFreshKey .bit (zeroContext
    ctx N).canonicalFreshKey_fresh
    (part5 tail) (fun entry =>
      let actual := (update5 tail record) entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation5 (model := model) (ctx := ctx) (N := N) tail record equation reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update4]
    rfl

private def part3 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model
  (expandedContext ctx N) (expandedContext ctx N) :=
  .workspace (expandedContext ctx N) (expandedContext ctx N).canonicalFreshKey (.unsignedWord
    (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh (part4 tail)

private def update3 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store (expandedContext ctx N)) :
    Store (expandedContext ctx N) × tail.Path :=
  let selected := (update4 tail record) (store.pushWorkspace (expandedContext ctx
    N).canonicalFreshKey (.unsignedWord (phaseBits N + 1)) (expandedContext ctx
      N).canonicalFreshKey_fresh)
  (Store.popWorkspace (expandedContext ctx N).canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    (expandedContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation3 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (expandedContext ctx N) Reference (model.HiddenState × History)) :
    (part3 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update3 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (expandedContext ctx N).canonicalFreshKey (.unsignedWord
    (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
    (part4 tail) (fun entry =>
      let actual := (update4 tail record) entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation4 (model := model) (ctx := ctx) (N := N) tail record equation reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update3]
    rfl

private def part2 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model
  (orderContext ctx N) (orderContext ctx N) :=
  .workspace (orderContext ctx N) (orderContext ctx N).canonicalFreshKey (.product .bit
    (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh (part3 tail)

private def update2 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store (orderContext ctx N)) :
    Store (orderContext ctx N) × tail.Path :=
  let selected := (update3 tail record) (store.pushWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (orderContext ctx N).canonicalFreshKey (.product .bit (.unsignedWord
    (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation2 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (orderContext ctx N) Reference (model.HiddenState × History)) :
    (part2 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update2 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (orderContext ctx N).canonicalFreshKey (.product .bit
    (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
    (part3 tail) (fun entry =>
      let actual := (update3 tail record) entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation3 (model := model) (ctx := ctx) (N := N) tail record equation reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update2]
    rfl

private def part1 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model
  (baseContext ctx N) (baseContext ctx N) :=
  .workspace (baseContext ctx N) (baseContext ctx N).canonicalFreshKey (.option (.unsignedWord
    (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh (part2 tail)

private def update1 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store (baseContext ctx N)) :
    Store (baseContext ctx N) × tail.Path :=
  let selected := (update2 tail record) (store.pushWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (baseContext ctx N).canonicalFreshKey (.option (.unsignedWord (phaseBits N +
    1))) (baseContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation1 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (baseContext ctx N) Reference (model.HiddenState × History)) :
    (part1 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update1 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (baseContext ctx N).canonicalFreshKey (.option
    (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
    (part2 tail) (fun entry =>
      let actual := (update2 tail record) entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation2 (model := model) (ctx := ctx) (N := N) tail record equation reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update1]
    rfl

private def part0 (tail : Circuit model (context ctx N) (context ctx N)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.canonicalResidue (modulusBits N))
    ctx.canonicalFreshKey_fresh (part1 tail)

private def update0 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store (context
  ctx N) → Store (context ctx N) × tail.Path) (store : Store ctx) :
    Store ctx × tail.Path :=
  let selected := (update1 tail record) (store.pushWorkspace ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.canonicalResidue (modulusBits N))
    ctx.canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation0 (tail : Circuit model (context ctx N) (context ctx N)) (record : Store
  (context ctx N) → Store (context ctx N) × tail.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (context ctx N) Reference (model.HiddenState × History)),
      tail.execute Reference state = state.mapClassical (fun entry =>
        let actual := record entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (part0 tail).execute Reference state = state.mapClassical (fun entry =>
      let actual := update0 tail record entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord ctx.canonicalFreshKey (.canonicalResidue (modulusBits N))
    ctx.canonicalFreshKey_fresh
    (part1 tail) (fun entry =>
      let actual := (update1 tail record) entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation1 (model := model) (ctx := ctx) (N := N) tail record equation reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update0]
    rfl

variable [BitWord.Selected model]

set_option maxHeartbeats 1000000 in
-- Retain the endpoint allowance for converting the full seven-cell path and store record.
/-- The full actual factor scope executes entry, the tail and release on arbitrary CQ states. -/
theorem code_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) source parameter phase output).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := step (model := model) source parameter phase output entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (equation0 (model := model) (ctx := ctx) (N := N) (body (model := model) source parameter
    phase output)
    (bodyStep (model := model) source parameter phase output)
    (body_execute (model := model) source parameter phase output) Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  dsimp only [update0, update1, update2, update3, update4, update5, update6, step, enter, leave]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
