/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Layout

/-!
# Actual stored-bit first-success control flow
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Copy the actual eligible candidate into the persistent selected word. -/
def selectedOp (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx candidate refs.selected

/-- Copy the actual true eligibility bit into the persistent accepted latch. -/
def acceptedOp (eligible : CInputRef ctx .bit) (refs : Refs ctx width) :
    ClassicalOp .bit .bit ctx ctx := .bit .copy ctx eligible refs.accepted

/-- The actual candidate-eligibility arm either writes both persistent outputs or does nothing. -/
def eligibleArm (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => .seq (.classical (selectedOp candidate refs))
      (.classical (acceptedOp eligible refs))

/-- The chosen eligibility arm's actual chronological store updates and instruction paths. -/
def eligibleArmStep (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (eligibleArm eligible candidate refs value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => ((store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs),
      ((), ()))

/-- Only a still-unaccepted result permits reading and acting on the actual candidate predicate. -/
def pendingArm (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    CShape.Value .bit → Circuit ctx ctx
  | .bit false => .branch eligible (eligibleArm eligible candidate refs)
  | .bit true => .id ctx

/-- The pending arm follows the real eligibility cell; an accepted result keeps its entire store. -/
def pendingArmStep (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pendingArm eligible candidate refs value).Path :=
  match value with
  | .bit false =>
      let chosen := eligibleArmStep eligible candidate refs (store.read eligible) store
      (chosen.1, ⟨store.read eligible, chosen.2⟩)
  | .bit true => (store, ())

/-- Read the real accepted latch before deciding whether any candidate write is still allowed. -/
def into (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord width))
    (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.accepted) (pendingArm eligible candidate refs)

/-- The complete actual store result and both actually selected branch histories. -/
def step (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord width))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx × (into eligible candidate refs).Path :=
  let chosen := pendingArmStep eligible candidate refs (store.read (writeInput refs.accepted)) store
  (chosen.1, ⟨store.read (writeInput refs.accepted), chosen.2⟩)

/-- The actual eligibility arm preserves complete incoming quantum-reference blocks. -/
theorem eligibleArm_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (eligibleArm eligible candidate refs value).execute Reference state =
      state.mapClassical (fun entry =>
        ((eligibleArmStep eligible candidate refs value entry.1).1,
          (entry.2, (eligibleArmStep eligible candidate refs value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · exact (Circuit.execute_id_mapClassical Reference state).trans (by
          congr 1
          exact Subsingleton.elim _ _)
      · simp only [eligibleArm, eligibleArmStep, Circuit.execute_seq,
          Circuit.execute_classical_mapClassical, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def]
        congr 1
        exact Subsingleton.elim _ _

/-- Actual pending selection reads the existing eligibility cell without computing a scratch
flag. -/
theorem pendingArm_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pendingArm eligible candidate refs value).execute Reference state =
      state.mapClassical (fun entry =>
        ((pendingArmStep eligible candidate refs value entry.1).1,
          (entry.2, (pendingArmStep eligible candidate refs value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · exact Circuit.execute_branch_mapClassical eligible (eligibleArm eligible candidate refs)
          (eligibleArmStep eligible candidate refs) (eligibleArm_execute eligible candidate refs)
          Reference state
      · exact (Circuit.execute_id_mapClassical Reference state).trans (by
          congr 1
          exact Subsingleton.elim _ _)

/-- The full actual first-success interpreter uses precisely the two existing stored predicates. -/
theorem into_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into eligible candidate refs).execute Reference state = state.mapClassical (fun entry =>
      ((step eligible candidate refs entry.1).1,
        (entry.2, (step eligible candidate refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical (writeInput refs.accepted)
    (pendingArm eligible candidate refs)
    (pendingArmStep eligible candidate refs) (pendingArm_execute eligible candidate refs)
    Reference state

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct
