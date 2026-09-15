/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition

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

/-- Closed conditional bodies retain or update the same real root cell. -/
def selectBody (refs : RoundRefs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit true => .id ctx
  | .bit false => .classical (copyOp refs)

/-- The comparison result is read from the actual written bit. -/
def select (refs : RoundRefs ctx width) : Circuit ctx ctx :=
  .branch (.storage refs.tooLarge.toCStorageRef) (selectBody refs)

/-- One literal native refinement round, with no auxiliary execution language. -/
def round (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (addOp refs))
    (.seq (.classical (squareOp refs))
      (.seq (.classical (compareOp input refs))
        (.seq (select refs) (.classical (shiftOp refs)))))

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Store and actual unique path of each closed conditional body. -/
def selectBodyStep (refs : RoundRefs ctx width) :
    (value : CShape.Value .bit) → Store ctx → Store ctx × (selectBody refs value).Path
  | .bit true, store => (store, ())
  | .bit false, store => (store.applyOp (copyOp refs), ())

/-- The branch records the same value that it actually reads. -/
def selectStep (refs : RoundRefs ctx width) (store : Store ctx) :
    Store ctx × (select refs).Path :=
  let value := store.read (.storage refs.tooLarge.toCStorageRef)
  let selected := selectBodyStep refs value store
  (selected.1, ⟨value, selected.2⟩)

/-- Complete actual selection preserves all incoming quantum-reference blocks. -/
theorem nativeSqrt_select_execute (refs : RoundRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (select refs).execute Reference state = state.mapClassical (fun entry =>
      ((selectStep refs entry.1).1, (entry.2, (selectStep refs entry.1).2))) := by
  have selected := Circuit.execute_branch_mapClassical
    (.storage refs.tooLarge.toCStorageRef) (selectBody refs) (selectBodyStep refs)
    (fun value reference {Past} _ initial => by
      cases value with
      | bit value =>
          cases value with
          | false =>
              refine (Circuit.execute_classical_mapClassical
                (copyOp refs) reference initial).trans ?_
              exact congrArg
                (fun equality : DecidableEq (Store ctx × (Past × Unit)) =>
                  @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register reference)
                    equality initial
                    (fun entry => (entry.1.applyOp (copyOp refs), (entry.2, ()))))
                (Subsingleton.elim _ _)
          | true =>
              refine (Circuit.execute_id_mapClassical reference initial).trans ?_
              exact congrArg
                (fun equality : DecidableEq (Store ctx × (Past × Unit)) =>
                  @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register reference)
                    equality initial (fun entry => (entry.1, (entry.2, ()))))
                (Subsingleton.elim _ _))
    Reference state
  refine selected.trans ?_
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (select refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry => ((selectStep refs entry.1).1, (entry.2, (selectStep refs entry.1).2))))
    (Subsingleton.elim _ _)

/-- The actual five-stage store update and chronological path. -/
def roundStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (store : Store ctx) : Store ctx × (round input refs).Path :=
  let added := store.applyOp (addOp refs)
  let squared := added.applyOp (squareOp refs)
  let compared := squared.applyOp (compareOp input refs)
  let selected := selectStep refs compared
  (selected.1.applyOp (shiftOp refs), ((), ((), ((), (selected.2, ())))))

/-- The real native round executes precisely that store update on every full reference block. -/
theorem nativeSqrt_round_execute (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (round input refs).execute Reference state = state.mapClassical (fun entry =>
      ((roundStep input refs entry.1).1, (entry.2, (roundStep input refs entry.1).2))) := by
  simp only [round, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    nativeSqrt_select_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (round input refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry =>
          ((roundStep input refs entry.1).1, (entry.2, (roundStep input refs entry.1).2))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
