/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Cursor.Lift
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Arithmetic

/-!
# Exact source observations after actual candidate materialization

The state here is the existing candidate-prefix record's store projection.
Its actual quotient and remainder retain the source Euclidean values, while
the continuant writes the fitted source candidate and preserves every other
persistent cursor coordinate and source validation input.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The actual candidate-prefix record's store, used by the existing complete visit. -/
def candidateState {width : Nat} (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (cursorDivisionShape width)) (store : Store ctx) : Store ctx :=
  (candidatePrefixStep (cellRead cells.cursor.numerator) (cellRead cells.cursor.denominator)
    (cellRead cells.cursor.previous) (cellRead cells.cursor.older)
    division cells.cursor.candidate store).1

/-- The same materialization record preserves every read outside its two actual destinations. -/
theorem nativeScan_candidateState_read_other {width : Nat}
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (cursorDivisionShape width)) {shape : CShape}
    (other : CInputRef ctx shape) (divisionFree : division.key ∉ other.storageKeys)
    (candidateFree : cells.cursor.candidate.key ∉ other.storageKeys) (store : Store ctx) :
    (candidateState cells division store).read other = store.read other :=
  nativeCandidatePrefix_read_other (cellRead cells.cursor.numerator)
    (cellRead cells.cursor.denominator) (cellRead cells.cursor.previous)
    (cellRead cells.cursor.older) division cells.cursor.candidate other
    divisionFree candidateFree store

/-- Materialization preserves all four actual source cursor coordinates. -/
theorem nativeScan_candidateState_cursor {width : Nat}
    (cells : ScanCells ctx modulusWidth width) (separated : cells.Separated)
    (division : CWriteRef ctx (cursorDivisionShape width))
    (divisionFree : ∀ key ∈ cells.writeKeys, division.key ≠ key)
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : CursorReads cells.cursor store cursor) :
    CursorReads cells.cursor (candidateState cells division store) cursor := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat (nativeScan_candidateState_read_other cells division
      (cellRead cells.cursor.numerator)
      (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 4 2 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.numerator
  · exact (congrArg CShape.Value.toNat (nativeScan_candidateState_read_other cells division
      (cellRead cells.cursor.denominator)
      (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 4 3 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.denominator
  · exact (congrArg CShape.Value.toNat (nativeScan_candidateState_read_other cells division
      (cellRead cells.cursor.older)
      (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 4 0 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.older
  · exact (congrArg CShape.Value.toNat (nativeScan_candidateState_read_other cells division
      (cellRead cells.cursor.previous)
      (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 4 1 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.previous

/-- The actual materialized word equals the fitted next source cursor candidate. -/
theorem nativeScan_candidateState_candidate {width : Nat}
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (cursorDivisionShape width))
    (divisionFree : ∀ key ∈ cells.writeKeys, division.key ≠ key)
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : CursorReads cells.cursor store cursor)
    (fits : cursor.candidate.denominator < 2 ^ width) :
    ((candidateState cells division store).read (cellRead cells.cursor.candidate)).toNat =
      cursor.candidate.denominator :=
  nativeCandidatePrefix_cursor (cellRead cells.cursor.numerator)
    (cellRead cells.cursor.denominator) (cellRead cells.cursor.previous)
    (cellRead cells.cursor.older) division cells.cursor.candidate
    (fun present => divisionFree _ (by simp [ScanCells.writeKeys]) (List.mem_singleton.mp present))
    (fun present => divisionFree _ (by simp [ScanCells.writeKeys]) (List.mem_singleton.mp present))
    store cursor reads.numerator reads.denominator reads.previous reads.older fits

/-- The retained division pair is exactly the result of the original two actual operand reads. -/
theorem nativeScan_candidateState_division {width : Nat}
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (cursorDivisionShape width))
    (different : cells.cursor.candidate.key ≠ division.key) (store : Store ctx) :
    (candidateState cells division store).read (cellRead division) =
      CShape.divRem width width
        (.product (store.read (cellRead cells.cursor.numerator))
          (store.read (cellRead cells.cursor.denominator))) := by
  unfold candidateState candidatePrefixStep
  exact (nativeScopedContinuant_read_other (.first (cellRead division))
    (cellRead cells.cursor.previous) (cellRead cells.cursor.older) cells.cursor.candidate
    (cellRead division) (fun present => different (List.mem_singleton.mp present))
    _).trans (Store.read_applyOp_output store
      (cursorDivision (cellRead cells.cursor.numerator)
        (cellRead cells.cursor.denominator) division))

/-- The actual retained remainder agrees with the same represented source Euclidean cursor. -/
theorem nativeScan_candidateState_remainder {width : Nat}
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (cursorDivisionShape width))
    (different : cells.cursor.candidate.key ≠ division.key) (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : CursorReads cells.cursor store cursor) :
    ((candidateState cells division store).read (.second (cellRead division))).toNat =
      cursor.remainder := by
  have actual := congrArg (fun value => value.second.toNat)
    (nativeScan_candidateState_division cells division different store)
  refine actual.trans ?_
  rw [nativeCursorDivision_second_exact, reads.numerator, reads.denominator]
  rfl

/-- The real prefix also preserves the source base and comparison constants. -/
theorem nativeScan_candidateState_source
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (division : CWriteRef ctx (cursorDivisionShape (phaseBits + 1)))
    (divisionBase : division.key ∉ base.storageKeys)
    (divisionZero : division.key ∉ cells.zero.storageKeys)
    (divisionOne : division.key ∉ cells.one.storageKeys)
    (candidateBase : cells.cursor.candidate.key ∉ base.storageKeys)
    (store : Store ctx) (reads : ScanSourceReads spec input base cells store) :
    ScanSourceReads spec input base cells (candidateState cells division store) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (nativeScan_candidateState_read_other cells division base divisionBase candidateBase
      store).trans reads.baseValue
  · exact (congrArg CShape.Value.toNat (nativeScan_candidateState_read_other cells division
      cells.zero divisionZero (separated.zeroFree _ (by simp [ScanCells.writeKeys])) store)).trans
        reads.zeroValue
  · exact (congrArg CShape.Value.toNat (nativeScan_candidateState_read_other cells division
      cells.one divisionOne (separated.oneFree _ (by simp [ScanCells.writeKeys])) store)).trans
        reads.oneValue

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
