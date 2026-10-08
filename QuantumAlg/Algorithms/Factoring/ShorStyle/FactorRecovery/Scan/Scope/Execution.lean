/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Scope.Store
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace.Record
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# One actual execution through all first-success scan scopes

Each true lexical layer consumes the shared workspace-record law. The whole
circuit executes the actual finite recovery scan and returns its matching
store and path, preserving every quantum-reference block. All four selector
heads are genuinely allocated and released in this same interpreter run.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private theorem body_execute (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) source inputs result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := bodyStep (model := model) source inputs result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (NativeFactorScan.code_execute (model := model) source (inputs.map liftInputs)
    (cells ctx N) (liftWrite result) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part3 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (selectedContext ctx N) (selectedContext ctx N) :=
  .workspace (selectedContext ctx N) (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh
    (body (model := model) source inputs result)

private def update3 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store
      (selectedContext ctx N)) :
    Store (selectedContext ctx N) × (body (model := model) source inputs result).Path :=
  let selected := bodyStep (model := model) source inputs result
    (store.pushWorkspace (selectedContext ctx N).canonicalFreshKey .bit (selectedContext ctx
      N).canonicalFreshKey_fresh)
  (Store.popWorkspace (selectedContext ctx N).canonicalFreshKey .bit (selectedContext ctx
    N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation3 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (selectedContext ctx N) Reference (model.HiddenState × History)) :
    (part3 (model := model) source inputs result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := update3 (model := model) source inputs result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh
    (body (model := model) source inputs result)
    (fun entry =>
      let actual := bodyStep (model := model) source inputs result entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact body_execute (model := model) source inputs result reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update3]

private def part2 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (acceptedContext ctx N) (acceptedContext ctx N) :=
  .workspace (acceptedContext ctx N) (acceptedContext ctx N).canonicalFreshKey (.unsignedWord
    (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
    (part3 (model := model) source inputs result)

private def update2 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store
      (acceptedContext ctx N)) :
    Store (acceptedContext ctx N) × (body (model := model) source inputs result).Path :=
  let selected := update3 (model := model) source inputs result
    (store.pushWorkspace (acceptedContext ctx N).canonicalFreshKey (.unsignedWord (modulusBits N))
      (acceptedContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (acceptedContext ctx N).canonicalFreshKey (.unsignedWord (modulusBits N))
    (acceptedContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation2 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (acceptedContext ctx N) Reference (model.HiddenState × History)) :
    (part2 (model := model) source inputs result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := update2 (model := model) source inputs result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (acceptedContext ctx N).canonicalFreshKey (.unsignedWord
    (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
    (part3 (model := model) source inputs result)
    (fun entry =>
      let actual := update3 (model := model) source inputs result entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation3 (model := model) source inputs result reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update2]
    rfl

private def part1 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (candidateContext ctx N) (candidateContext ctx N) :=
  .workspace (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 (model := model) source inputs result)

private def update1 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store
      (candidateContext ctx N)) :
    Store (candidateContext ctx N) × (body (model := model) source inputs result).Path :=
  let selected := update2 (model := model) source inputs result
    (store.pushWorkspace (candidateContext ctx N).canonicalFreshKey .bit (candidateContext ctx
      N).canonicalFreshKey_fresh)
  (Store.popWorkspace (candidateContext ctx N).canonicalFreshKey .bit (candidateContext ctx
    N).canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation1 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (candidateContext ctx N) Reference (model.HiddenState × History)) :
    (part1 (model := model) source inputs result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := update1 (model := model) source inputs result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 (model := model) source inputs result)
    (fun entry =>
      let actual := update2 (model := model) source inputs result entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation2 (model := model) source inputs result reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update1]
    rfl

private def part0 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.product .bit (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh
    (part1 (model := model) source inputs result)

private def update0 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (body (model := model) source inputs result).Path :=
  let selected := update1 (model := model) source inputs result
    (store.pushWorkspace ctx.canonicalFreshKey (.product .bit (.unsignedWord (modulusBits N)))
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.product .bit (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh selected.1, selected.2)

private theorem equation0 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (part0 (model := model) source inputs result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := update0 (model := model) source inputs result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_workspaceRecord ctx.canonicalFreshKey (.product .bit (.unsignedWord
    (modulusBits N))) ctx.canonicalFreshKey_fresh
    (part1 (model := model) source inputs result)
    (fun entry =>
      let actual := update1 (model := model) source inputs result entry.1
      ((actual.1, entry.2), actual.2))
    ?bodyEquation Reference state).trans ?_
  · intro reference history _ input
    dsimp only
    exact equation1 (model := model) source inputs result reference input
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [Circuit.workspaceRecord, update0]
    rfl

/-- The complete scan executes and releases all four real workspace entries. -/
theorem code_execute (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) source inputs result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := step (model := model) source inputs result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (equation0 (model := model) source inputs result Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  dsimp only [update0, update1, update2, update3, step, enter, leave]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope
