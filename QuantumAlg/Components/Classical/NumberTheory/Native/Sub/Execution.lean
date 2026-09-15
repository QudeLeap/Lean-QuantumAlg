/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit

/-!
# Complete execution of the native saturating subtraction

The deterministic update below follows the actual comparison, selected word
instruction and matching lexical release. Its history is the real circuit
path, including the stored decision. The execution equation retains every
incoming quantum-reference block and all correlations with the original store.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Each selected native instruction returns its actual store and unit path. -/
def selectedStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (value : CShape.Value .bit) → Store (context ctx) →
      Store (context ctx) × (selected left right output value).Path
  | .bit true, store => (store.applyOp (clearOp output), ())
  | .bit false, store => (store.applyOp (subtractOp left right output), ())

/-- The actual branch records the same comparison value that it reads. -/
def branchStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx)) :
    Store (context ctx) ×
      (Circuit.branch (.storage (decision ctx).toCStorageRef) (selected left right output)).Path :=
  let value := store.read (.storage (decision ctx).toCStorageRef)
  let result := selectedStep left right output value store
  (result.1, ⟨value, result.2⟩)

private theorem selected_equation (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx) Reference History) :
    (selected left right output value).execute Reference state =
      state.mapClassical (fun entry =>
        ((selectedStep left right output value entry.1).1,
          (entry.2, (selectedStep left right output value entry.1).2))) := by
  cases value with
  | bit flag =>
      cases flag
      all_goals
        refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
        exact congrArg
          (fun equality : DecidableEq (Store (context ctx) × (History × Unit)) =>
            @ExecutionState.mapClassical _ _ _ _
              (Register.prod (context ctx).register Reference) equality state _)
          (Subsingleton.elim _ _)

private theorem branch_equation (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx) Reference History) :
    (Circuit.branch (.storage (decision ctx).toCStorageRef)
      (selected left right output)).execute Reference state =
        state.mapClassical (fun entry =>
          ((branchStep left right output entry.1).1,
            (entry.2, (branchStep left right output entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical
    (.storage (decision ctx).toCStorageRef) (selected left right output)
    (selectedStep left right output) (selected_equation left right output) Reference state).trans ?_
  exact congrArg
    (fun equality : DecidableEq (Store (context ctx) ×
        (History × (Circuit.branch (.storage (decision ctx).toCStorageRef)
          (selected left right output)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _
        (Register.prod (context ctx).register Reference) equality state
        (fun entry => ((branchStep left right output entry.1).1,
          (entry.2, (branchStep left right output entry.1).2))))
    (Subsingleton.elim _ _)

/-- The body performs its real comparison before the selected output instruction. -/
def bodyStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx)) :
    Store (context ctx) × (body left right output).Path :=
  let result := branchStep left right output (store.applyOp (compareOp left right))
  (result.1, ((), result.2))

/-- The actual body preserves the full incoming quantum-reference state in every classical block. -/
theorem nativeSub_body_execute (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx) Reference History) :
    (body left right output).execute Reference state = state.mapClassical (fun entry =>
      ((bodyStep left right output entry.1).1,
        (entry.2, (bodyStep left right output entry.1).2))) := by
  simp only [body, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    branch_equation, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact congrArg
    (fun equality : DecidableEq
        (Store (context ctx) × (History × (body left right output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _
        (Register.prod (context ctx).register Reference) equality state
        (fun entry => ((bodyStep left right output entry.1).1,
          (entry.2, (bodyStep left right output entry.1).2))))
    (Subsingleton.elim _ _)

/-- Actual lexical entry, body execution and release of the one decision cell. -/
def intoStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into left right output).Path :=
  let entered := store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let result := bodyStep left right output entered
  (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh result.1, result.2)

/-- Every actual execution agrees with the complete store update and its genuine finite path. -/
theorem nativeSub_into_execute (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into left right output).execute Reference state = state.mapClassical (fun entry =>
      ((intoStep left right output entry.1).1,
        (entry.2, (intoStep left right output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (body left right output) (bodyStep left right output)
    (nativeSub_body_execute left right output) Reference state).trans ?_
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (into left right output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry => ((intoStep left right output entry.1).1,
          (entry.2, (intoStep left right output entry.1).2))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
