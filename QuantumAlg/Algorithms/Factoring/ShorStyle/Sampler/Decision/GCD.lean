/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Arms
import all QuantumAlg.Components.Classical.NumberTheory.GCD.LexicalSemantics

/-!
# Exact execution of the accepted residue's native GCD arm

The accepted arm widens the preserved candidate, runs the expanded Euclidean
program in its actual temporary scopes, builds the comparison operand from
the stored default unit, and selects the real result arm. Its store equation
uses the actual GCD loop and path; no arithmetic classification instruction
or assumed scratch initialization replaces any part of the execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def oneOp (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.extended

private def coprimeOp (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) .bit ctx ctx :=
  .wordBinary .equal (width + 1) ctx
    (.product (FirstAccepted.cellRead gcdResult) (FirstAccepted.cellRead scratch.extended))
    scratch.positive

private def resultTail (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .seq (.classical (oneOp shared scratch))
    (.seq (.classical (coprimeOp scratch gcdResult)) (chooseResult shared scratch gcdResult))

private def resultTailStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (resultTail shared scratch gcdResult).Path :=
  let compared := (store.applyOp (oneOp shared scratch)).applyOp (coprimeOp scratch gcdResult)
  let selected := resultStep shared scratch gcdResult compared
  (selected.1, ((), ((), selected.2)))

private theorem resultTail_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (resultTail shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry => ((resultTailStep shared scratch gcdResult entry.1).1,
        (entry.2, (resultTailStep shared scratch gcdResult entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (oneOp shared scratch))
    (.seq (.classical (coprimeOp scratch gcdResult)) (chooseResult shared scratch gcdResult))
    (fun store => (store.applyOp (oneOp shared scratch), ()))
    (fun store =>
      let next := resultStep shared scratch gcdResult (store.applyOp (coprimeOp scratch gcdResult))
      (next.1, ((), next.2)))
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (oneOp shared scratch) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_seq_mapClassical (.classical (coprimeOp scratch gcdResult))
        (chooseResult shared scratch gcdResult)
        (fun store => (store.applyOp (coprimeOp scratch gcdResult), ()))
        (resultStep shared scratch gcdResult)
        (fun reference {_} _ initial => by
          refine (Circuit.execute_classical_mapClassical
            (coprimeOp scratch gcdResult) reference initial).trans ?_
          congr 1
          exact Subsingleton.elim _ _)
        (decisionResult_execute shared scratch gcdResult) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private def gcdTail (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .seq (NumberTheory.GCD.lexicalBody
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
    (resultTail shared scratch gcdResult)

private def gcdTailStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (gcdTail shared scratch gcdResult).Path :=
  let reduced := NumberTheory.GCD.lexicalStep
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult store
  let selected := resultTailStep shared scratch gcdResult reduced.1
  (selected.1, (reduced.2, selected.2))

private theorem gcdTail_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (gcdTail shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry => ((gcdTailStep shared scratch gcdResult entry.1).1,
        (entry.2, (gcdTailStep shared scratch gcdResult entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical _ (resultTail shared scratch gcdResult)
    (NumberTheory.GCD.lexicalStep
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
    (resultTailStep shared scratch gcdResult)
    (NumberTheory.GCD.gcdLexical_execute
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
    (resultTail_execute shared scratch gcdResult) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Exact store and path of widening, the actual Euclidean scopes, and the stored result arm. -/
def acceptedStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (acceptedBody shared scratch gcdResult).Path :=
  let selected := gcdTailStep shared scratch gcdResult (store.applyOp (Proposal.extendOp scratch))
  (selected.1, ((), selected.2))

/-- The full accepted arm executes its real GCD path and preserves all joint matrix blocks. -/
theorem decisionAccepted_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (acceptedBody shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry => ((acceptedStep shared scratch gcdResult entry.1).1,
        (entry.2, (acceptedStep shared scratch gcdResult entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (Proposal.extendOp scratch))
    (gcdTail shared scratch gcdResult)
    (fun store => (store.applyOp (Proposal.extendOp scratch), ()))
    (gcdTailStep shared scratch gcdResult)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (Proposal.extendOp scratch) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (gcdTail_execute shared scratch gcdResult) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
