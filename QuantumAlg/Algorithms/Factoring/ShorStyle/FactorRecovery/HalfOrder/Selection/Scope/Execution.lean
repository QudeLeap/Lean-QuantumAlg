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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

-- Bound only elaboration of these concrete nested path dictionaries, not execution resources.
private def part5 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (upperContext ctx N) (upperContext ctx N) :=
  .workspace (upperContext ctx N) (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    (body halfPower output)

private def update5 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (upperContext ctx N)) :
    Store (upperContext ctx N) × (part5 halfPower output).Path :=
  let selected := (bodyStep halfPower output)
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
    (initial : State (upperContext ctx N) reference history) :
    (part5 halfPower output).execute reference initial = initial.mapClassical (fun entry =>
      ((update5 halfPower output entry.1).1, (entry.2, (update5 halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh
    (body halfPower output) (bodyStep halfPower output) (body_execute halfPower output)
    reference initial).trans ?_
  dsimp only [update5]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (upperContext ctx N) × history)
    (D := Store (upperContext ctx N) × (history × (part5 halfPower output).Path))
    (R := Register.prod (upperContext ctx N).register reference) _ initial _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (upperContext ctx N) × history)
    (D := Store (upperContext ctx N) × (history × (part5 halfPower output).Path))
    (R := Register.prod (upperContext ctx N).register reference) _ initial _).symm

private def part4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (lowerContext ctx N) (lowerContext ctx N) :=
  .workspace (lowerContext ctx N) (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh (part5 halfPower output)

private def update4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (lowerContext ctx N)) :
    Store (lowerContext ctx N) × (part4 halfPower output).Path :=
  let selected := (update5 halfPower output)
    (store.pushWorkspace (lowerContext ctx N).canonicalFreshKey
      .bit (lowerContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation4 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (lowerContext ctx N) reference history) :
    (part4 halfPower output).execute reference initial = initial.mapClassical (fun entry =>
      ((update4 halfPower output entry.1).1, (entry.2, (update4 halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
    (part5 halfPower output) (update5 halfPower output)
    (equation5 halfPower output) reference initial).trans ?_
  dsimp only [update4]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (lowerContext ctx N) × history)
    (D := Store (lowerContext ctx N) × (history × (part4 halfPower output).Path))
    (R := Register.prod (lowerContext ctx N).register reference) _ initial _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (lowerContext ctx N) × history)
    (D := Store (lowerContext ctx N) × (history × (part4 halfPower output).Path))
    (R := Register.prod (lowerContext ctx N).register reference) _ initial _).symm

private def part3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (modulusContext ctx N) (modulusContext ctx N) :=
  .workspace (modulusContext ctx N) (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh (part4 halfPower output)

private def update3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (modulusContext ctx N)) :
    Store (modulusContext ctx N) × (part3 halfPower output).Path :=
  let selected := (update4 halfPower output)
    (store.pushWorkspace (modulusContext ctx N).canonicalFreshKey
      .bit (modulusContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation3 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (modulusContext ctx N) reference history) :
    (part3 halfPower output).execute reference initial = initial.mapClassical (fun entry =>
      ((update3 halfPower output entry.1).1, (entry.2, (update3 halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
    (part4 halfPower output) (update4 halfPower output)
    (equation4 halfPower output) reference initial).trans ?_
  dsimp only [update3]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (modulusContext ctx N) × history)
    (D := Store (modulusContext ctx N) × (history × (part3 halfPower output).Path))
    (R := Register.prod (modulusContext ctx N).register reference) _ initial _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (modulusContext ctx N) × history)
    (D := Store (modulusContext ctx N) × (history × (part3 halfPower output).Path))
    (R := Register.prod (modulusContext ctx N).register reference) _ initial _).symm

private def part2 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (oneContext ctx N) (oneContext ctx N) :=
  .workspace (oneContext ctx N) (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    (part3 halfPower output)

private def update2 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (oneContext ctx N)) :
    Store (oneContext ctx N) × (part2 halfPower output).Path :=
  let selected := (update3 halfPower output)
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
    (initial : State (oneContext ctx N) reference history) :
    (part2 halfPower output).execute reference initial = initial.mapClassical (fun entry =>
      ((update2 halfPower output entry.1).1, (entry.2, (update2 halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
    (part3 halfPower output) (update3 halfPower output)
    (equation3 halfPower output) reference initial).trans ?_
  dsimp only [update2]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (oneContext ctx N) × history)
    (D := Store (oneContext ctx N) × (history × (part2 halfPower output).Path))
    (R := Register.prod (oneContext ctx N).register reference) _ initial _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (oneContext ctx N) × history)
    (D := Store (oneContext ctx N) × (history × (part2 halfPower output).Path))
    (R := Register.prod (oneContext ctx N).register reference) _ initial _).symm

private def part1 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (candidateContext ctx N) (candidateContext ctx N) :=
  .workspace (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 halfPower output)

private def update1 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (candidateContext ctx N)) :
    Store (candidateContext ctx N) × (part1 halfPower output).Path :=
  let selected := (update2 halfPower output)
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
    (initial : State (candidateContext ctx N) reference history) :
    (part1 halfPower output).execute reference initial = initial.mapClassical (fun entry =>
      ((update1 halfPower output entry.1).1, (entry.2, (update1 halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 halfPower output) (update2 halfPower output)
    (equation2 halfPower output) reference initial).trans ?_
  dsimp only [update1]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (candidateContext ctx N) × history)
    (D := Store (candidateContext ctx N) × (history × (part1 halfPower output).Path))
    (R := Register.prod (candidateContext ctx N).register reference) _ initial _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (candidateContext ctx N) × history)
    (D := Store (candidateContext ctx N) × (history × (part1 halfPower output).Path))
    (R := Register.prod (candidateContext ctx N).register reference) _ initial _).symm

private def part0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (part1 halfPower output)

private def update0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) :
    Store ctx × (part0 halfPower output).Path :=
  let selected := (update1 halfPower output)
    (store.pushWorkspace ctx.canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh selected.1, selected.2)

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
private theorem equation0 (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State ctx reference history) :
    (part0 halfPower output).execute reference initial = initial.mapClassical (fun entry =>
      ((update0 halfPower output entry.1).1, (entry.2, (update0 halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (part1 halfPower output) (update1 halfPower output)
    (equation1 halfPower output) reference initial).trans ?_
  dsimp only [update0]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × history)
    (D := Store ctx × (history × (part0 halfPower output).Path))
    (R := Register.prod ctx.register reference) _ initial _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × history)
    (D := Store ctx × (history × (part0 halfPower output).Path))
    (R := Register.prod ctx.register reference) _ initial _).symm

set_option maxHeartbeats 1000000 in
-- Normalizing the actual nested workspace path dictionaries exceeds the default elaboration limit.
/-- The actual complete lexical factor program executes its real store and physical path. -/
theorem code_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((step halfPower output entry.1).1,
        (entry.2, (step halfPower output entry.1).2))) := by
  refine (equation0 halfPower output Reference state).trans ?_
  dsimp only [update0, update1, update2, update3, update4, update5, step, enter, leave]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code halfPower output).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code halfPower output).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
