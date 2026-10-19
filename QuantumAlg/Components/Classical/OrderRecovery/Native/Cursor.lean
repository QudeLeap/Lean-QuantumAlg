/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Candidate.Prefix
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Actual Euclidean cursor and recovery-latch updates

A rejected candidate advances four stored words and computes the next active
bit from the actual stored remainder. Acceptance copies the actual candidate
and validation bit into the result latches and clears activity. These are
ordinary closed classical instructions, with no mathematical cursor opcode.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The six actual writable cells carrying one Euclidean continuant cursor. -/
structure CursorCells (ctx : RuntimeCtx kind) (width : Nat) where
  numerator : CWriteRef ctx (.unsignedWord width)
  denominator : CWriteRef ctx (.unsignedWord width)
  older : CWriteRef ctx (.unsignedWord width)
  previous : CWriteRef ctx (.unsignedWord width)
  candidate : CWriteRef ctx (.unsignedWord width)
  active : CWriteRef ctx .bit

/-- A real fixed-width copy between the specified stored cursor words. -/
def copyCursorWord (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx input output

/-- Compute activity by comparing actual zero and the current divisor word. -/
def cursorActiveOp (cells : CursorCells ctx width)
    (zero : CInputRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product zero (cellRead cells.denominator)) cells.active

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Rejecting a candidate rotates the real operands and recomputes activity. -/
def advanceCursor (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
      (copyCursorWord (cellRead cells.previous) cells.older))
    (.seq (BitWord.instruction (execution := model)
      (copyCursorWord (cellRead cells.candidate) cells.previous))
      (.seq (BitWord.instruction (execution := model)
      (copyCursorWord (cellRead cells.denominator) cells.numerator))
        (.seq (BitWord.instruction (execution := model)
      (copyCursorWord remainder cells.denominator))
          (BitWord.instruction (execution := model) (cursorActiveOp cells zero)))))

/-- The actual five-instruction cursor store update. -/
def advanceCursorStore {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (copyCursorWord (cellRead cells.previous) cells.older)).applyOp
    (copyCursorWord (cellRead cells.candidate) cells.previous)).applyOp
      (copyCursorWord (cellRead cells.denominator) cells.numerator)).applyOp
        (copyCursorWord remainder cells.denominator)).applyOp (cursorActiveOp cells zero)

/-- Actual returned records from all five cursor instructions. -/
def advanceCursorStep (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (advanceCursor (model := model) cells remainder zero).Path :=
  let first := BitWord.instructionStep (execution := model)
    (copyCursorWord (cellRead cells.previous) cells.older) store
  let second := BitWord.instructionStep (execution := model)
    (copyCursorWord (cellRead cells.candidate) cells.previous) first.1
  let third := BitWord.instructionStep (execution := model)
    (copyCursorWord (cellRead cells.denominator) cells.numerator) second.1
  let fourth := BitWord.instructionStep (execution := model)
    (copyCursorWord remainder cells.denominator) third.1
  let fifth := BitWord.instructionStep (execution := model) (cursorActiveOp cells zero) fourth.1
  (fifth.1, (first.2, (second.2, (third.2, (fourth.2, fifth.2)))))

/-- Each full classical/quantum/reference block follows the actual cursor instructions. -/
lemma nativeCursor_advance_execute (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (advanceCursor (model := model) cells remainder zero).execute environment Reference state =
      state.mapClassical (fun entry =>
        (advanceCursorStore cells remainder zero entry.1,
          (entry.2.1, (entry.2.2,
            (advanceCursorStep (model := model) cells remainder zero entry.1).2)))) := by
  simp only [advanceCursor, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual rejected-candidate trace has four word copies and one comparison. -/
lemma nativeCursor_advance_eventTrace (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width))
    (path : (advanceCursor (model := model) cells remainder zero).Path) :
    (advanceCursor (model := model) cells remainder zero).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .lessThan width))] := by
  simp only [advanceCursor, Circuit.eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- All five actual cursor-update instructions are sequentially dependent. -/
lemma nativeCursor_advance_unitDepth (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width))
    (path : (advanceCursor (model := model) cells remainder zero).Path) :
    (advanceCursor (model := model) cells remainder zero).depth (fun _ => 1) path = 5 := by
  rcases path with ⟨first, second, third, fourth, fifth⟩
  simp only [advanceCursor, Circuit.depth_seq, BitWord.bitWord_instruction_depth]

/-- Cursor writes preserve the entire real borrowed classical value. -/
lemma nativeCursor_advance_borrowed_values {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    (advanceCursorStore cells remainder zero store).readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [advanceCursorStore, Store.readBorrowedClassical_applyOp]

/-- Acceptance copies the actual candidate and success bit before clearing the active latch. -/
def acceptCursor (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
      (copyCursorWord candidate selected))
    (.seq (BitWord.instruction (execution := model) (.bit .copy ctx valid accepted))
      (BitWord.instruction (execution := model) (.bit .not ctx valid active)))

/-- The actual three-instruction acceptance store. -/
def acceptCursorStore {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) (store : Store ctx) : Store ctx :=
  ((store.applyOp (copyCursorWord candidate selected)).applyOp
    (.bit .copy ctx valid accepted)).applyOp (.bit .not ctx valid active)

/-- Actual candidate copy, success copy and activity negation records. -/
def acceptCursorStep (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (acceptCursor (model := model) candidate valid selected accepted active).Path :=
  let first := BitWord.instructionStep (execution := model)
    (copyCursorWord candidate selected) store
  let second := BitWord.instructionStep (execution := model) (.bit .copy ctx valid accepted) first.1
  let third := BitWord.instructionStep (execution := model) (.bit .not ctx valid active) second.1
  (third.1, (first.2, (second.2, third.2)))

/-- Acceptance acts on each complete density block through its actual three writes. -/
lemma nativeCursor_accept_execute (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (acceptCursor (model := model) candidate valid selected accepted active).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        (acceptCursorStore candidate valid selected accepted active entry.1,
          (entry.2.1, (entry.2.2,
            (acceptCursorStep (model := model) candidate valid selected accepted active
              entry.1).2)))) := by
  simp only [acceptCursor, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual accepted-candidate trace retains its word copy, bit copy and negation. -/
lemma nativeCursor_accept_eventTrace (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit)
    (path : (acceptCursor (model := model) candidate valid selected accepted active).Path) :
    (acceptCursor (model := model) candidate valid selected accepted active).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.bit .copy)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.bit .not))] := by
  simp only [acceptCursor, Circuit.eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Acceptance has the exact unit depth of its three actual dependent operations. -/
lemma nativeCursor_accept_unitDepth (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit)
    (path : (acceptCursor (model := model) candidate valid selected accepted active).Path) :
    (acceptCursor (model := model) candidate valid selected accepted active).depth
      (fun _ => 1) path = 3 := by
  rcases path with ⟨first, second, third⟩
  simp only [acceptCursor, Circuit.depth_seq, BitWord.bitWord_instruction_depth]

/-- Acceptance preserves the complete actual borrowed classical value. -/
lemma nativeCursor_accept_borrowed_values {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) (store : Store ctx) :
    (acceptCursorStore candidate valid selected accepted active store).readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [acceptCursorStore, Store.readBorrowedClassical_applyOp]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
