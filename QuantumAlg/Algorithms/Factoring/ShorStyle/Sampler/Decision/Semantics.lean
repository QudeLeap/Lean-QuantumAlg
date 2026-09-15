/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.GCD
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization

/-!
# Exact execution of the complete residue preparation decision

The equation composes the real initialization, stored acceptance branch,
expanded GCD arm, and final parameter write. It records the actual selected
path and preserves every complete quantum-reference matrix block. The store
map is obtained from those instructions on arbitrary incoming storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def acceptanceChoiceStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx ×
      (if value.toBool then acceptedBody shared scratch gcdResult
        else .classical (clearWordOp scratch.candidate)).Path :=
  match value with
  | .bit false => (store.applyOp (clearWordOp scratch.candidate), ())
  | .bit true => acceptedStep shared scratch gcdResult store

private theorem acceptanceChoice_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (if value.toBool then acceptedBody shared scratch gcdResult
      else .classical (clearWordOp scratch.candidate)).execute Reference state =
        state.mapClassical (fun entry =>
          ((acceptanceChoiceStep shared scratch gcdResult value entry.1).1,
            (entry.2, (acceptanceChoiceStep shared scratch gcdResult value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, acceptanceChoiceStep]
        refine (Circuit.execute_classical_mapClassical
          (clearWordOp scratch.candidate) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [CShape.Value.toBool, acceptanceChoiceStep]
        refine (decisionAccepted_execute shared scratch gcdResult Reference state).trans ?_
        congr 1

/-- The actual acceptance cell selects the computed GCD arm or one real payload-clearing write. -/
def acceptanceStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (chooseAccepted shared scratch gcdResult).Path :=
  let value := store.read (FirstAccepted.cellRead shared.selector.accepted)
  let selected := acceptanceChoiceStep shared scratch gcdResult value store
  (selected.1, ⟨value, selected.2⟩)

/-- Actual stored acceptance controls the full selected matrix-preserving execution. -/
theorem decisionAcceptance_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (chooseAccepted shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry => ((acceptanceStep shared scratch gcdResult entry.1).1,
        (entry.2, (acceptanceStep shared scratch gcdResult entry.1).2))) := by
  exact Circuit.execute_branch_mapClassical (FirstAccepted.cellRead shared.selector.accepted)
    (fun value => if value.toBool then acceptedBody shared scratch gcdResult
      else .classical (clearWordOp scratch.candidate))
    (acceptanceChoiceStep shared scratch gcdResult)
    (acceptanceChoice_execute shared scratch gcdResult) Reference state

/-- Forgetting the real branch path exposes exactly the store selected by the acceptance bit. -/
theorem decisionAcceptance_store (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptanceStep shared scratch gcdResult store).1 =
      if (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool then
        (acceptedStep shared scratch gcdResult store).1
      else store.applyOp (clearWordOp scratch.candidate) := by
  cases value : store.read (FirstAccepted.cellRead shared.selector.accepted) with
  | bit bit =>
      dsimp only [acceptanceStep]
      rw [value]
      cases bit <;> rfl

private def packedTailStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    Store ctx × (Circuit.seq (chooseAccepted shared scratch gcdResult)
      (.classical (packOp shared scratch output))).Path :=
  let selected := acceptanceStep shared scratch gcdResult store
  (selected.1.applyOp (packOp shared scratch output), (selected.2, ()))

private theorem packedTail_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (chooseAccepted shared scratch gcdResult)
      (.classical (packOp shared scratch output))).execute Reference state =
        state.mapClassical (fun entry =>
          ((packedTailStep shared scratch gcdResult output entry.1).1,
          (entry.2, (packedTailStep shared scratch gcdResult output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (chooseAccepted shared scratch gcdResult)
    (.classical (packOp shared scratch output)) (acceptanceStep shared scratch gcdResult)
    (fun store => (store.applyOp (packOp shared scratch output), ()))
    (decisionAcceptance_execute shared scratch gcdResult)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (packOp shared scratch output) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Store and actual nested instruction path of the complete decision and parameter write. -/
def step (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    Store ctx × (circuit shared scratch gcdResult output).Path :=
  let final := packedTailStep shared scratch gcdResult output
    (initializationStore shared scratch store)
  (final.1, (((), ((), ((), ()))), final.2))

/-- The complete decision preserves every reference correlation under its exact store map. -/
theorem decision_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (circuit shared scratch gcdResult output).execute Reference state =
      state.mapClassical (fun entry => ((step shared scratch gcdResult output entry.1).1,
        (entry.2, (step shared scratch gcdResult output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (initializeBody shared scratch) _
    (fun store => (initializationStore shared scratch store, ((), ((), ((), ())))))
    (packedTailStep shared scratch gcdResult output)
    (fun reference {_} _ initial => by
      refine (decisionInitialization_execute shared scratch reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (packedTail_execute shared scratch gcdResult output) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
