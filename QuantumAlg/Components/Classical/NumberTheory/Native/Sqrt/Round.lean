/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual native binary-refinement square-root round

The round adds the current increment to the root, squares that candidate
with the full-width multiplication instruction, compares against the widened
original input, copies the candidate only when its square is small enough,
and shifts the increment right. Every step uses the existing circuit and
store interpreter. This leaf states its complete action on every input
store and external reference; arithmetic interval facts are proved separately.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual working cells consumed by one square-root refinement round. -/
structure RoundRefs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Current lower estimate. -/
  root : CWriteRef ctx (.unsignedWord width)
  /-- Current binary increment. -/
  half : CWriteRef ctx (.unsignedWord width)
  /-- Full candidate word computed by the addition. -/
  candidate : CWriteRef ctx (.unsignedWord width)
  /-- Complete square, with twice the operand width. -/
  square : CWriteRef ctx (.unsignedWord (width + width))
  /-- The actual strict comparison result controls whether the candidate is copied. -/
  tooLarge : CWriteRef ctx .bit

/-- Candidate addition on the actual root and increment. -/
def addOp (refs : RoundRefs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .add width ctx
    (.product (.storage refs.root.toCStorageRef) (.storage refs.half.toCStorageRef)) refs.candidate

/-- Full multiplication retains every bit of the candidate square. -/
def squareOp (refs : RoundRefs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord (width + width)) ctx ctx :=
  .mulFull width width ctx
    (.product (.storage refs.candidate.toCStorageRef) (.storage refs.candidate.toCStorageRef))
    refs.square

/-- The stored comparison asks whether the original input is strictly below the candidate square. -/
def compareOp (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) :
    ClassicalOp (.product (.unsignedWord (width + width)) (.unsignedWord (width + width)))
      .bit ctx ctx :=
  .wordBinary .lessThan (width + width) ctx
    (.product input (.storage refs.square.toCStorageRef)) refs.tooLarge

/-- The successful branch actually overwrites the root with the tested candidate. -/
def copyOp (refs : RoundRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (.storage refs.candidate.toCStorageRef) refs.root

/-- One real shift prepares the next binary increment. -/
def shiftOp (refs : RoundRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (.storage refs.half.toCStorageRef) refs.half

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Closed conditional bodies retain or update the same real root cell. -/
def selectBody (refs : RoundRefs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit true => .id ctx
  | .bit false => BitWord.instruction (execution := model) (copyOp refs)

/-- The comparison result is read from the actual written bit. -/
def select (refs : RoundRefs ctx width) : Circuit model ctx ctx :=
  .branch (.storage refs.tooLarge.toCStorageRef) (selectBody (model := model) refs)

/-- One literal native refinement round, with no auxiliary execution language. -/
def round (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (addOp refs))
    (.seq (BitWord.instruction (execution := model) (squareOp refs))
      (.seq (BitWord.instruction (execution := model) (compareOp input refs))
        (.seq (select (model := model) refs) (BitWord.instruction (execution := model) (shiftOp
          refs)))))

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Store and actual returned path of each closed conditional body. -/
def selectBodyStep (refs : RoundRefs ctx width) :
    (value : CShape.Value .bit) → Store ctx → Store ctx × (selectBody (model := model) refs
      value).Path
  | .bit true, store => (store, ())
  | .bit false, store => BitWord.instructionStep (execution := model) (copyOp refs) store

/-- The branch records the same value that it actually reads. -/
def selectStep (refs : RoundRefs ctx width) (store : Store ctx) :
    Store ctx × (select (model := model) refs).Path :=
  let value := store.read (.storage refs.tooLarge.toCStorageRef)
  let selected := selectBodyStep (model := model) refs value store
  (selected.1, ⟨value, selected.2⟩)

/-- Complete actual selection preserves all incoming quantum-reference blocks. -/
theorem nativeSqrt_select_execute (refs : RoundRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (select (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      ((selectStep (model := model) refs entry.1).1, (entry.2.1, (entry.2.2, (selectStep (model :=
        model) refs entry.1).2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (.storage refs.tooLarge.toCStorageRef) (selectBody (model := model) refs)
    (fun flag before =>
      let actual := selectBodyStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun value reference _history _ initial => by
      cases value with
      | bit flag =>
          cases flag
          · exact BitWord.bitWord_instruction_execute _ initial
          · exact (Circuit.execute_id_mapClassical reference initial).trans
              (ExecutionState.executionState_mapClassical_congr _ rfl))
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual five-stage store update and chronological path. -/
def roundStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (store : Store ctx) : Store ctx × (round (model := model) input
      refs).Path :=
  let added := BitWord.instructionStep (execution := model) (addOp refs) store
  let squared := BitWord.instructionStep (execution := model) (squareOp refs) added.1
  let compared := BitWord.instructionStep (execution := model) (compareOp input refs) squared.1
  let selected := selectStep (model := model) refs compared.1
  let shifted := BitWord.instructionStep (execution := model) (shiftOp refs) selected.1
  (shifted.1, (added.2, (squared.2, (compared.2, (selected.2, shifted.2)))))

/-- The real native round executes precisely that store update on every full reference block. -/
theorem nativeSqrt_round_execute (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (round (model := model) input refs).execute Reference state = state.mapClassical (fun entry =>
      ((roundStep (model := model) input refs entry.1).1, (entry.2.1, (entry.2.2, (roundStep
        (model := model) input refs entry.1).2)))) := by
  simp only [round, roundStep, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    nativeSqrt_select_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
