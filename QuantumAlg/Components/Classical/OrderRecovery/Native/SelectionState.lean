/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Validation.State

/-!
# Actual acceptance and rejected-candidate cursor updates

A true validation bit copies the real candidate and freezes the scan. A
false validation bit rotates the actual cursor words and tests its actual
remainder. The resulting observations are precisely the original source
cursor advancement or the selected candidate, with no reconstructed input.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The actual result word and both stored latches record a selected candidate. -/
structure ChosenCursorReads (cells : ScanCells ctx modulusWidth (phaseBits + 1))
    (store : Store ctx) (candidate : Nat) : Prop where
  /-- The actual selected word contains that candidate. -/
  selected : (store.read (cellRead cells.selected)).toNat = candidate
  /-- The result latch has actually been set. -/
  accepted : store.read (cellRead cells.accepted) = .bit true
  /-- All remaining finite slots will read the actual false activity bit. -/
  inactive : store.read (cellRead cells.cursor.active) = .bit false

/-- The actual acceptance instructions copy the real candidate and freeze further visits. -/
lemma nativeScan_accept_chosen
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (store : Store ctx) (candidate : Nat)
    (candidateValue : (store.read (cellRead cells.cursor.candidate)).toNat = candidate)
    (validValue : store.read (cellRead cells.valid) = .bit true) :
    ChosenCursorReads cells
      (acceptCursorStore (cellRead cells.cursor.candidate) (cellRead cells.valid)
        cells.selected cells.accepted cells.cursor.active store) candidate := by
  have actual := nativeCursor_accept_reads (cellRead cells.cursor.candidate) (cellRead cells.valid)
    cells.selected cells.accepted cells.cursor.active
    (nativeScan_separated_keys cells separated 5 6 (by decide))
    (nativeScan_separated_keys cells separated 5 7 (by decide))
    (nativeScan_separated_keys cells separated 7 6 (by decide))
    (fun present => nativeScan_separated_keys cells separated 6 10 (by decide)
      (List.mem_singleton.mp present))
    (fun present => nativeScan_separated_keys cells separated 7 10 (by decide)
      (List.mem_singleton.mp present)) store
  refine ⟨(congrArg CShape.Value.toNat actual.1).trans candidateValue,
    actual.2.1.trans validValue, ?_⟩
  rw [validValue] at actual
  exact actual.2.2

/-- Rejection advances the same source cursor and preserves the false accepted latch. -/
lemma nativeScan_advance_pending
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (remainder : CInputRef ctx (.unsignedWord (phaseBits + 1)))
    (remainderFree : ∀ key ∈ [cells.cursor.older.key, cells.cursor.previous.key,
      cells.cursor.numerator.key], key ∉ remainder.storageKeys)
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : CursorReads cells.cursor store cursor)
    (candidateValue : (store.read (cellRead cells.cursor.candidate)).toNat =
      cursor.candidate.denominator)
    (remainderValue : (store.read remainder).toNat = cursor.remainder)
    (zeroValue : (store.read cells.zero).toNat = 0)
    (acceptedValue : store.read (cellRead cells.accepted) = .bit false) :
    PendingCursorReads cells (advanceCursorStore cells.cursor remainder cells.zero store)
      cursor.advance := by
  have distinct : [cells.cursor.older.key, cells.cursor.previous.key, cells.cursor.numerator.key,
      cells.cursor.denominator.key, cells.cursor.candidate.key, cells.cursor.active.key].Nodup :=
    List.Pairwise.take (i := 6) separated.distinct
  have zeroFree : ∀ key ∈ [cells.cursor.older.key, cells.cursor.previous.key,
      cells.cursor.numerator.key, cells.cursor.denominator.key], key ∉ cells.zero.storageKeys := by
    intro key member
    apply separated.zeroFree key
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [ScanCells.writeKeys]
  have actual := nativeCursor_advance_reads cells.cursor remainder cells.zero distinct
    remainderFree zeroFree store
  refine ⟨⟨(congrArg CShape.Value.toNat actual.2.2.1).trans reads.denominator,
    (congrArg CShape.Value.toNat actual.2.2.2.1).trans remainderValue,
    (congrArg CShape.Value.toNat actual.1).trans reads.previous,
    (congrArg CShape.Value.toNat actual.2.1).trans candidateValue⟩, ?_, ?_⟩
  · refine actual.2.2.2.2.trans ?_
    rw [zeroValue, remainderValue]
    simp only [ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor.active,
      ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor.advance,
      Nat.pos_iff_ne_zero]
    rfl
  · refine (nativeCursor_advance_read_other cells.cursor remainder cells.zero
      (cellRead cells.accepted) ?_ store).trans acceptedValue
    intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact fun present => nativeScan_separated_keys cells separated 0 7 (by decide)
        (List.mem_singleton.mp present)
    · exact fun present => nativeScan_separated_keys cells separated 1 7 (by decide)
        (List.mem_singleton.mp present)
    · exact fun present => nativeScan_separated_keys cells separated 2 7 (by decide)
        (List.mem_singleton.mp present)
    · exact fun present => nativeScan_separated_keys cells separated 3 7 (by decide)
        (List.mem_singleton.mp present)
    · exact fun present => nativeScan_separated_keys cells separated 5 7 (by decide)
        (List.mem_singleton.mp present)

/-- Every remaining actual slot preserves the complete store once a candidate has been selected. -/
lemma nativeScan_chosen_frozen {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx) (candidate : Nat)
    (chosen : ChosenCursorReads cells store candidate) (fuel : Nat) :
    ChosenCursorReads cells
      ((fun initial => (scanSlotStep (model := model) spec base cells initial).1)^[fuel]
        store) candidate := by
  rw [nativeScan_iterate_of_inactive spec base cells store chosen.inactive fuel]
  exact chosen

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
