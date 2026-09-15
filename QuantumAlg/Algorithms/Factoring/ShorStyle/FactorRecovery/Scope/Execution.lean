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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private def part6 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (positiveContext ctx N) (positiveContext ctx N) :=
  .workspace (positiveContext ctx N) (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh
    (body source parameter phase output)

private def update6 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (positiveContext ctx N)) :
    Store (positiveContext ctx N) × (part6 source parameter phase output).Path :=
  Circuit.workspaceRecord (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N))
    (positiveContext ctx N).canonicalFreshKey_fresh
    (body source parameter phase output) (bodyStep source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation6 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (positiveContext ctx N) reference history) :
    (part6 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update6 source parameter phase output entry.1).1,
        (entry.2, (update6 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N))
    (positiveContext ctx N).canonicalFreshKey_fresh
    (body source parameter phase output) (bodyStep source parameter phase output)
    (body_execute source parameter phase output) reference initial

private def part5 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (activeContext ctx N) (activeContext ctx N) :=
  .workspace (activeContext ctx N) (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
    (part6 source parameter phase output)

private def update5 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (activeContext ctx N)) :
    Store (activeContext ctx N) × (part5 source parameter phase output).Path :=
  Circuit.workspaceRecord (activeContext ctx N).canonicalFreshKey
    .bit
    (activeContext ctx N).canonicalFreshKey_fresh
    (part6 source parameter phase output) (update6 source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation5 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (activeContext ctx N) reference history) :
    (part5 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update5 source parameter phase output entry.1).1,
        (entry.2, (update5 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord (activeContext ctx N).canonicalFreshKey
    .bit
    (activeContext ctx N).canonicalFreshKey_fresh
    (part6 source parameter phase output) (update6 source parameter phase output)
    (equation6 source parameter phase output) reference initial

private def part4 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (zeroContext ctx N) (zeroContext ctx N) :=
  .workspace (zeroContext ctx N) (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
    (part5 source parameter phase output)

private def update4 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (zeroContext ctx N)) :
    Store (zeroContext ctx N) × (part4 source parameter phase output).Path :=
  Circuit.workspaceRecord (zeroContext ctx N).canonicalFreshKey
    .bit
    (zeroContext ctx N).canonicalFreshKey_fresh
    (part5 source parameter phase output) (update5 source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation4 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (zeroContext ctx N) reference history) :
    (part4 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update4 source parameter phase output entry.1).1,
        (entry.2, (update4 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord (zeroContext ctx N).canonicalFreshKey
    .bit
    (zeroContext ctx N).canonicalFreshKey_fresh
    (part5 source parameter phase output) (update5 source parameter phase output)
    (equation5 source parameter phase output) reference initial

private def part3 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (expandedContext ctx N) (expandedContext ctx N) :=
  .workspace (expandedContext ctx N) (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
    (part4 source parameter phase output)

private def update3 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (expandedContext ctx N)) :
    Store (expandedContext ctx N) × (part3 source parameter phase output).Path :=
  Circuit.workspaceRecord (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1))
    (expandedContext ctx N).canonicalFreshKey_fresh
    (part4 source parameter phase output) (update4 source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation3 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (expandedContext ctx N) reference history) :
    (part3 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update3 source parameter phase output entry.1).1,
        (entry.2, (update3 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1))
    (expandedContext ctx N).canonicalFreshKey_fresh
    (part4 source parameter phase output) (update4 source parameter phase output)
    (equation4 source parameter phase output) reference initial

private def part2 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (orderContext ctx N) (orderContext ctx N) :=
  .workspace (orderContext ctx N) (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1)))
    (orderContext ctx N).canonicalFreshKey_fresh
    (part3 source parameter phase output)

private def update2 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (orderContext ctx N)) :
    Store (orderContext ctx N) × (part2 source parameter phase output).Path :=
  Circuit.workspaceRecord (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1)))
    (orderContext ctx N).canonicalFreshKey_fresh
    (part3 source parameter phase output) (update3 source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation2 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (orderContext ctx N) reference history) :
    (part2 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update2 source parameter phase output entry.1).1,
        (entry.2, (update2 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1)))
    (orderContext ctx N).canonicalFreshKey_fresh
    (part3 source parameter phase output) (update3 source parameter phase output)
    (equation3 source parameter phase output) reference initial

private def part1 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (baseContext ctx N) (baseContext ctx N) :=
  .workspace (baseContext ctx N) (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
    (part2 source parameter phase output)

private def update1 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (baseContext ctx N)) :
    Store (baseContext ctx N) × (part1 source parameter phase output).Path :=
  Circuit.workspaceRecord (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1)))
    (baseContext ctx N).canonicalFreshKey_fresh
    (part2 source parameter phase output) (update2 source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation1 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State (baseContext ctx N) reference history) :
    (part1 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update1 source parameter phase output entry.1).1,
        (entry.2, (update1 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1)))
    (baseContext ctx N).canonicalFreshKey_fresh
    (part2 source parameter phase output) (update2 source parameter phase output)
    (equation2 source parameter phase output) reference initial

private def part0 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh
    (part1 source parameter phase output)

private def update0 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) :
    Store ctx × (part0 source parameter phase output).Path :=
  Circuit.workspaceRecord ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N))
    ctx.canonicalFreshKey_fresh
    (part1 source parameter phase output) (update1 source parameter phase output) store

set_option maxHeartbeats 1000000 in
-- Elaborating these actual nested path dictionaries requires a larger bounded local allowance.
private theorem equation0 (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (reference : Register) {history : Type} [Fintype history]
    (initial : State ctx reference history) :
    (part0 source parameter phase output).execute reference initial =
      initial.mapClassical (fun entry => ((update0 source parameter phase output entry.1).1,
        (entry.2, (update0 source parameter phase output entry.1).2))) :=
  Circuit.execute_workspaceRecord ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N))
    ctx.canonicalFreshKey_fresh
    (part1 source parameter phase output) (update1 source parameter phase output)
    (equation1 source parameter phase output) reference initial

set_option maxHeartbeats 1000000 in
-- The seven real scope records are aligned with the exact original full-circuit path here.
/-- The full actual factor scope executes real entry, the tail and release on arbitrary CQ. -/
theorem code_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code source parameter phase output).execute Reference state =
      state.mapClassical (fun entry => ((step source parameter phase output entry.1).1,
        (entry.2, (step source parameter phase output entry.1).2))) := by
  refine (equation0 source parameter phase output Reference state).trans ?_
  dsimp only [update0, update1, update2, update3, update4, update5, update6,
    Circuit.workspaceRecord, step, enter, leave]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code source parameter phase output).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code source parameter phase output).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
