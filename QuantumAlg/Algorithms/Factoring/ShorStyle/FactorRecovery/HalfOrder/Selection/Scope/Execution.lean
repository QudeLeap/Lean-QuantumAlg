/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.BodyExecution
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete execution through the six actual half-factor workspace scopes

Each application below uses the existing single-workspace interpreter law.
The private circuit terms are exactly the successive tails of the same actual
six-scope program. Every real allocation and release remains in its execution,
and the final record includes the original quantum-reference density blocks.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

-- Bound only elaboration of these concrete nested path dictionaries, not execution resources.
private def part5 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (upperContext ctx N) (upperContext ctx N) :=
  .workspace (upperContext ctx N) (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    (body (model := model) halfPower output)

private def update5 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (upperContext ctx N)) :
    Store (upperContext ctx N) × (body (model := model) halfPower output).Path :=
  let selected := (bodyStep (model := model) halfPower output)
    (store.pushWorkspace (upperContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation5 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (upperContext ctx N) reference (model.HiddenState × history)) :
    (part5 (model := model) halfPower output).execute reference initial = initial.mapClassical
        (fun entry =>
      ((update5 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update5
          (model := model) halfPower output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    (body (model := model) halfPower output)
    (fun entry =>
      let actual := bodyStep (model := model) halfPower output entry.1
      ((actual.1, entry.2), actual.2))
    (body_execute (model := model) halfPower output) reference initial).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (lowerContext ctx N) (lowerContext ctx N) :=
  .workspace (lowerContext ctx N) (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh (part5 (model := model) halfPower output)

private def update4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (lowerContext ctx N)) :
    Store (lowerContext ctx N) × (body (model := model) halfPower output).Path :=
  let selected := (update5 (model := model) halfPower output)
    (store.pushWorkspace (lowerContext ctx N).canonicalFreshKey
      .bit (lowerContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (lowerContext ctx N) reference (model.HiddenState × history)) :
    (part4 (model := model) halfPower output).execute reference initial = initial.mapClassical
        (fun entry =>
      ((update4 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update4
          (model := model) halfPower output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
    (part5 (model := model) halfPower output)
    (fun entry =>
      let actual := update5 (model := model) halfPower output entry.1
      ((actual.1, entry.2), actual.2))
    (equation5 (model := model) halfPower output) reference initial).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (modulusContext ctx N) (modulusContext ctx N) :=
  .workspace (modulusContext ctx N) (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh (part4 (model := model) halfPower output)

private def update3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (modulusContext ctx N)) :
    Store (modulusContext ctx N) × (body (model := model) halfPower output).Path :=
  let selected := (update4 (model := model) halfPower output)
    (store.pushWorkspace (modulusContext ctx N).canonicalFreshKey
      .bit (modulusContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (modulusContext ctx N) reference (model.HiddenState × history)) :
    (part3 (model := model) halfPower output).execute reference initial = initial.mapClassical
        (fun entry =>
      ((update3 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update3
          (model := model) halfPower output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
    (part4 (model := model) halfPower output)
    (fun entry =>
      let actual := update4 (model := model) halfPower output entry.1
      ((actual.1, entry.2), actual.2))
    (equation4 (model := model) halfPower output) reference initial).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part2 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (oneContext ctx N) (oneContext ctx N) :=
  .workspace (oneContext ctx N) (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    (part3 (model := model) halfPower output)

private def update2 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (oneContext ctx N)) :
    Store (oneContext ctx N) × (body (model := model) halfPower output).Path :=
  let selected := (update3 (model := model) halfPower output)
    (store.pushWorkspace (oneContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation2 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (oneContext ctx N) reference (model.HiddenState × history)) :
    (part2 (model := model) halfPower output).execute reference initial = initial.mapClassical
        (fun entry =>
      ((update2 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update2
          (model := model) halfPower output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    (part3 (model := model) halfPower output)
    (fun entry =>
      let actual := update3 (model := model) halfPower output entry.1
      ((actual.1, entry.2), actual.2))
    (equation3 (model := model) halfPower output) reference initial).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part1 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (candidateContext ctx N) (candidateContext ctx N) :=
  .workspace (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 (model := model) halfPower output)

private def update1 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (candidateContext ctx N)) :
    Store (candidateContext ctx N) × (body (model := model) halfPower output).Path :=
  let selected := (update2 (model := model) halfPower output)
    (store.pushWorkspace (candidateContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation1 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (candidateContext ctx N) reference (model.HiddenState × history)) :
    (part1 (model := model) halfPower output).execute reference initial = initial.mapClassical
        (fun entry =>
      ((update1 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update1
          (model := model) halfPower output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 (model := model) halfPower output)
    (fun entry =>
      let actual := update2 (model := model) halfPower output entry.1
      ((actual.1, entry.2), actual.2))
    (equation2 (model := model) halfPower output) reference initial).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def part0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (part1 (model := model) halfPower output)

private def update0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) :
    Store ctx × (body (model := model) halfPower output).Path :=
  let selected := (update1 (model := model) halfPower output)
    (store.pushWorkspace ctx.canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State ctx reference (model.HiddenState × history)) :
    (part0 (model := model) halfPower output).execute reference initial = initial.mapClassical
        (fun entry =>
      ((update0 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update0
          (model := model) halfPower output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (part1 (model := model) halfPower output)
    (fun entry =>
      let actual := update1 (model := model) halfPower output entry.1
      ((actual.1, entry.2), actual.2))
    (equation1 (model := model) halfPower output) reference initial).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
/-- The actual complete lexical factor program executes its real store and physical path. -/
theorem code_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((step (model := model) halfPower output entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) halfPower output entry.1).2)))) := by
  refine (equation0 (model := model) halfPower output Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
