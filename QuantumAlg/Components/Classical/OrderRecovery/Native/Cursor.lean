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

/-- Rejecting a candidate rotates the real operands and recomputes activity. -/
def advanceCursor (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (copyCursorWord (cellRead cells.previous) cells.older))
    (.seq (.classical (copyCursorWord (cellRead cells.candidate) cells.previous))
      (.seq (.classical (copyCursorWord (cellRead cells.denominator) cells.numerator))
        (.seq (.classical (copyCursorWord remainder cells.denominator))
          (.classical (cursorActiveOp cells zero)))))

/-- The actual five-instruction cursor store update. -/
def advanceCursorStore (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (copyCursorWord (cellRead cells.previous) cells.older)).applyOp
    (copyCursorWord (cellRead cells.candidate) cells.previous)).applyOp
      (copyCursorWord (cellRead cells.denominator) cells.numerator)).applyOp
        (copyCursorWord remainder cells.denominator)).applyOp (cursorActiveOp cells zero)

/-- Each full classical/quantum/reference block follows the actual cursor instructions. -/
theorem nativeCursor_advance_execute (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (advanceCursor cells remainder zero).execute Reference state =
      state.mapClassical (fun entry =>
        (advanceCursorStore cells remainder zero entry.1,
          (entry.2, ((), ((), ((), ((), ()))))))) := by
  simp only [advanceCursor, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual rejected-candidate trace has four word copies and one comparison. -/
theorem nativeCursor_advance_eventTrace (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width))
    (path : (advanceCursor cells remainder zero).Path) :
    (advanceCursor cells remainder zero).eventTrace path =
      [.classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordBinary .lessThan width)] := rfl

/-- All five actual cursor-update instructions are sequentially dependent. -/
theorem nativeCursor_advance_unitDepth (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width))
    (path : (advanceCursor cells remainder zero).Path) :
    (advanceCursor cells remainder zero).depth (fun _ => 1) path = 5 := rfl

/-- Cursor writes preserve the entire real borrowed classical value. -/
theorem nativeCursor_advance_borrowed_values (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    (advanceCursorStore cells remainder zero store).readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [advanceCursorStore, Store.readBorrowedClassical_applyOp]

/-- Acceptance copies the actual candidate and success bit before clearing the active latch. -/
def acceptCursor (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) : Circuit ctx ctx :=
  .seq (.classical (copyCursorWord candidate selected))
    (.seq (.classical (.bit .copy ctx valid accepted))
      (.classical (.bit .not ctx valid active)))

/-- The actual three-instruction acceptance store. -/
def acceptCursorStore (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) (store : Store ctx) : Store ctx :=
  ((store.applyOp (copyCursorWord candidate selected)).applyOp
    (.bit .copy ctx valid accepted)).applyOp (.bit .not ctx valid active)

/-- Acceptance acts on each complete density block through its actual three writes. -/
theorem nativeCursor_accept_execute (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (acceptCursor candidate valid selected accepted active).execute Reference state =
      state.mapClassical (fun entry =>
        (acceptCursorStore candidate valid selected accepted active entry.1,
          (entry.2, ((), ((), ()))))) := by
  simp only [acceptCursor, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual accepted-candidate trace retains its word copy, bit copy and negation. -/
theorem nativeCursor_accept_eventTrace (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit)
    (path : (acceptCursor candidate valid selected accepted active).Path) :
    (acceptCursor candidate valid selected accepted active).eventTrace path =
      [.classicalOperation (.wordUnary .copy width), .classicalOperation (.bit .copy),
        .classicalOperation (.bit .not)] := rfl

/-- Acceptance has the exact unit depth of its three actual dependent operations. -/
theorem nativeCursor_accept_unitDepth (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit)
    (path : (acceptCursor candidate valid selected accepted active).Path) :
    (acceptCursor candidate valid selected accepted active).depth (fun _ => 1) path = 3 := rfl

/-- Acceptance preserves the complete actual borrowed classical value. -/
theorem nativeCursor_accept_borrowed_values (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) (store : Store ctx) :
    (acceptCursorStore candidate valid selected accepted active store).readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [acceptCursorStore, Store.readBorrowedClassical_applyOp]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
