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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem body_execute (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body source inputs result).execute Reference state =
      state.mapClassical (fun entry => ((bodyStep source inputs result entry.1).1,
        (entry.2, (bodyStep source inputs result entry.1).2))) := by
  refine (NativeFactorScan.code_execute source (inputs.map liftInputs)
    (cells ctx N) (liftWrite result) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store (context ctx N) × (History × (body source inputs result).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((bodyStep source inputs result entry.1).1,
          (entry.2, (bodyStep source inputs result entry.1).2)))) (Subsingleton.elim _ _)

private def part3 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (selectedContext ctx N) (selectedContext ctx N) :=
  .workspace (selectedContext ctx N) (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh (body source inputs result)

private def update3 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (selectedContext ctx N)) :
    Store (selectedContext ctx N) × (part3 source inputs result).Path :=
  Circuit.workspaceRecord (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
    (body source inputs result) (bodyStep source inputs result) store

private theorem equation3 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (selectedContext ctx N) Reference History) :
    (part3 source inputs result).execute Reference state =
      state.mapClassical (fun entry => ((update3 source inputs result entry.1).1,
        (entry.2, (update3 source inputs result entry.1).2))) :=
  Circuit.execute_workspaceRecord (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
    (body source inputs result) (bodyStep source inputs result)
    (body_execute source inputs result) Reference state

private def part2 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (acceptedContext ctx N) (acceptedContext ctx N) :=
  .workspace (acceptedContext ctx N) (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N))
    (acceptedContext ctx N).canonicalFreshKey_fresh
    (part3 source inputs result)

private def update2 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (acceptedContext ctx N)) :
    Store (acceptedContext ctx N) × (part2 source inputs result).Path :=
  Circuit.workspaceRecord (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
    (part3 source inputs result) (update3 source inputs result) store

private theorem equation2 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (acceptedContext ctx N) Reference History) :
    (part2 source inputs result).execute Reference state =
      state.mapClassical (fun entry => ((update2 source inputs result entry.1).1,
        (entry.2, (update2 source inputs result entry.1).2))) :=
  Circuit.execute_workspaceRecord (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
    (part3 source inputs result) (update3 source inputs result)
    (equation3 source inputs result) Reference state

private def part1 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (candidateContext ctx N) (candidateContext ctx N) :=
  .workspace (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey
    .bit (candidateContext ctx N).canonicalFreshKey_fresh (part2 source inputs result)

private def update1 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (candidateContext ctx N)) :
    Store (candidateContext ctx N) × (part1 source inputs result).Path :=
  Circuit.workspaceRecord (candidateContext ctx N).canonicalFreshKey
    .bit (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 source inputs result) (update2 source inputs result) store

private theorem equation1 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (candidateContext ctx N) Reference History) :
    (part1 source inputs result).execute Reference state =
      state.mapClassical (fun entry => ((update1 source inputs result entry.1).1,
        (entry.2, (update1 source inputs result entry.1).2))) :=
  Circuit.execute_workspaceRecord (candidateContext ctx N).canonicalFreshKey
    .bit (candidateContext ctx N).canonicalFreshKey_fresh
    (part2 source inputs result) (update2 source inputs result)
    (equation2 source inputs result) Reference state

private def part0 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh
    (part1 source inputs result)

private def update0 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (part0 source inputs result).Path :=
  Circuit.workspaceRecord ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
    (part1 source inputs result) (update1 source inputs result) store

private theorem equation0 (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (part0 source inputs result).execute Reference state =
      state.mapClassical (fun entry => ((update0 source inputs result entry.1).1,
        (entry.2, (update0 source inputs result entry.1).2))) :=
  Circuit.execute_workspaceRecord ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
    (part1 source inputs result) (update1 source inputs result)
    (equation1 source inputs result) Reference state

/-- The actual complete scan scope executes entry, every recovery visit and matching release. -/
theorem code_execute (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code source inputs result).execute Reference state =
      state.mapClassical (fun entry => ((step source inputs result entry.1).1,
        (entry.2, (step source inputs result entry.1).2))) := by
  refine (equation0 source inputs result Reference state).trans ?_
  dsimp only [update0, update1, update2, update3, Circuit.workspaceRecord, step, enter, leave]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code source inputs result).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code source inputs result).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope
