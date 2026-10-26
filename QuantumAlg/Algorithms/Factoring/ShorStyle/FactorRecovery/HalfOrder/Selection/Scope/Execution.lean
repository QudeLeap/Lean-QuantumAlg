/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.BodyExecution
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

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

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

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
  Circuit.workspaceStoreRecord (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    (body (model := model) halfPower output)
    (bodyStep (model := model) halfPower output) store

private lemma equation5 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (upperContext ctx N) reference (model.HiddenState × history)) :
    (part5 (model := model) halfPower output).execute
      environment reference initial = initial.mapClassical
        (fun entry =>
      ((update5 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update5
          (model := model) halfPower output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord environment
    (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    (body (model := model) halfPower output)
    (bodyStep (model := model) halfPower output)
    (body_execute (model := model) halfPower output) reference initial

private def part4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (lowerContext ctx N) (lowerContext ctx N) :=
  .workspace (lowerContext ctx N) (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh (part5 (model := model) halfPower output)

private def update4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (lowerContext ctx N)) :
    Store (lowerContext ctx N) × (body (model := model) halfPower output).Path :=
  Circuit.workspaceStoreRecord (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
    (part5 (model := model) halfPower output)
    (update5 (model := model) halfPower output) store

private lemma equation4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (lowerContext ctx N) reference (model.HiddenState × history)) :
    (part4 (model := model) halfPower output).execute
      environment reference initial = initial.mapClassical
        (fun entry =>
      ((update4 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update4
          (model := model) halfPower output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord environment
    (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
    (part5 (model := model) halfPower output)
    (update5 (model := model) halfPower output)
    (equation5 (model := model) halfPower output) reference initial

private def part3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit model (modulusContext ctx N) (modulusContext ctx N) :=
  .workspace (modulusContext ctx N) (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh (part4 (model := model) halfPower output)

private def update3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (modulusContext ctx N)) :
    Store (modulusContext ctx N) × (body (model := model) halfPower output).Path :=
  Circuit.workspaceStoreRecord (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
    (part4 (model := model) halfPower output)
    (update4 (model := model) halfPower output) store

private lemma equation3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (modulusContext ctx N) reference (model.HiddenState × history)) :
    (part3 (model := model) halfPower output).execute
      environment reference initial = initial.mapClassical
        (fun entry =>
      ((update3 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update3
          (model := model) halfPower output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord environment
    (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
    (part4 (model := model) halfPower output)
    (update4 (model := model) halfPower output)
    (equation4 (model := model) halfPower output) reference initial

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
  Circuit.workspaceStoreRecord (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    (part3 (model := model) halfPower output)
    (update3 (model := model) halfPower output) store

private lemma equation2 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (oneContext ctx N) reference (model.HiddenState × history)) :
    (part2 (model := model) halfPower output).execute
      environment reference initial = initial.mapClassical
        (fun entry =>
      ((update2 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update2
          (model := model) halfPower output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord environment
    (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    (part3 (model := model) halfPower output)
    (update3 (model := model) halfPower output)
    (equation3 (model := model) halfPower output) reference initial

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
  Circuit.workspaceStoreRecord (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 (model := model) halfPower output)
    (update2 (model := model) halfPower output) store

private lemma equation1 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (candidateContext ctx N) reference (model.HiddenState × history)) :
    (part1 (model := model) halfPower output).execute
      environment reference initial = initial.mapClassical
        (fun entry =>
      ((update1 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update1
          (model := model) halfPower output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord environment
    (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 (model := model) halfPower output)
    (update2 (model := model) halfPower output)
    (equation2 (model := model) halfPower output) reference initial

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
  Circuit.workspaceStoreRecord ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (part1 (model := model) halfPower output)
    (update1 (model := model) halfPower output) store

private lemma equation0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State ctx reference (model.HiddenState × history)) :
    (part0 (model := model) halfPower output).execute
      environment reference initial = initial.mapClassical
        (fun entry =>
      ((update0 (model := model) halfPower output entry.1).1, (entry.2.1, (entry.2.2, (update0
          (model := model) halfPower output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord environment
    ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (part1 (model := model) halfPower output)
    (update1 (model := model) halfPower output)
    (equation1 (model := model) halfPower output) reference initial

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
/-- The actual complete lexical factor program executes its real store and physical path. -/
lemma code_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) halfPower output).execute environment Reference state =
      state.mapClassical (fun entry => ((step (model := model) halfPower output entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) halfPower output entry.1).2)))) := by
  refine (equation0 (model := model) halfPower output Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
