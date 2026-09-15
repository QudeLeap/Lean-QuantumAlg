/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Exact block semantics of the native first-accepted selector

The real decision writes and stored branch determine one exact store and path
update. Its equality preserves every incoming quantum-reference matrix block,
including arbitrary correlations. Semantic separation of the selected latches
is proved separately; this execution equation holds for all supplied references.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The two real Boolean instructions update the full state without altering its quantum block. -/
theorem firstAccepted_decision_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (decisionBody inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        (decisionStore inputs refs entry.1, (entry.2, ((), ())))) := by
  simp only [decisionBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual selected arm copies the word and take latch with the exact two-instruction path. -/
theorem firstAccepted_copy_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (copyBody inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        (copyStore inputs refs entry.1, (entry.2, ((), ())))) := by
  simp only [copyBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private def copyChoiceStep (inputs : Inputs ctx width) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) : Store ctx ×
      (if value.toBool then copyBody inputs refs else Circuit.id ctx).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => (copyStore inputs refs store, ((), ()))

private theorem copyChoice_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (if value.toBool then copyBody inputs refs else Circuit.id ctx).execute Reference state =
      state.mapClassical (fun entry =>
        ((copyChoiceStep inputs refs value entry.1).1,
          (entry.2, (copyChoiceStep inputs refs value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, copyChoiceStep]
        refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [CShape.Value.toBool, copyChoiceStep]
        refine (firstAccepted_copy_execute inputs refs Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _

/-- The store and dependent path chosen by the actual take bit. -/
def conditionalStep (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx × (conditionalCopy inputs refs).Path :=
  let value := store.read (cellRead refs.take)
  let selected := copyChoiceStep inputs refs value store
  (selected.1, ⟨value, selected.2⟩)

/-- The branch maps each input block through its own stored take value. -/
theorem firstAccepted_conditional_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (conditionalCopy inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((conditionalStep inputs refs entry.1).1,
          (entry.2, (conditionalStep inputs refs entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (cellRead refs.take) _
    (copyChoiceStep inputs refs) (copyChoice_execute inputs refs) Reference state).trans ?_
  congr 1

/-- The concrete store and real nested path of the complete selector. -/
def step (inputs : Inputs ctx width) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (circuit inputs refs).Path :=
  let selected := conditionalStep inputs refs (decisionStore inputs refs store)
  (selected.1, (((), ()), selected.2))

/-- The selector's complete state is the exact actual store map on every external reference. -/
theorem firstAccepted_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (circuit inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((step inputs refs entry.1).1, (entry.2, (step inputs refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (decisionBody inputs refs) (conditionalCopy inputs refs)
    (fun store => (decisionStore inputs refs store, ((), ()))) (conditionalStep inputs refs)
    (fun reference {_} _ initial => by
      refine (firstAccepted_decision_execute inputs refs reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (firstAccepted_conditional_execute inputs refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete store update is the real decision followed by its selected or empty copy arm. -/
theorem firstAccepted_step_store (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) :
    (step inputs refs store).1 =
      let decision := decisionStore inputs refs store
      if (decision.read (cellRead refs.take)).toBool then
        copyStore inputs refs decision else decision := by
  dsimp only [step, conditionalStep]
  cases value : (decisionStore inputs refs store).read (cellRead refs.take) with
  | bit bit => cases bit <;> rfl

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
