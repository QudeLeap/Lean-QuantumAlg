/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.VisitState

/-!
# Source-correct active visits through the genuine lexical division scope

The fresh workspace head supplies every internal division-separation fact.
Structural pushes and pops preserve the original cursor and selected-result
observations. The resulting active-visit theorem has only source read and
ordinary persistent-placement assumptions, proved by the complete recovery
layout and initialization.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

private lemma cell_key_mem {shape : CShape} (cell : CWriteRef ctx shape) :
    cell.key ∈ ctx.keys :=
  (cellRead cell).storageKeys_subset_context (List.mem_singleton_self cell.key)

/-- Every persistent scan write is an actual cell of the current context. -/
lemma nativeScan_writeKeys_subset_context {width : Nat}
    (cells : ScanCells ctx modulusWidth width) : cells.writeKeys ⊆ ctx.keys := by
  intro key member
  simp only [ScanCells.writeKeys, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cell_key_mem cells.cursor.older
  · exact cell_key_mem cells.cursor.previous
  · exact cell_key_mem cells.cursor.numerator
  · exact cell_key_mem cells.cursor.denominator
  · exact cell_key_mem cells.cursor.candidate
  · exact cell_key_mem cells.cursor.active
  · exact cell_key_mem cells.selected
  · exact cell_key_mem cells.accepted
  · exact cell_key_mem cells.power
  · exact cell_key_mem cells.positive
  · exact cell_key_mem cells.valid

/-- The actual fresh division head is different from every persistent lifted write. -/
lemma nativeScan_division_writeKeys_separate {width : Nat}
    (cells : ScanCells ctx modulusWidth width) :
    ∀ key ∈ (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape width)
      ctx.canonicalFreshKey_fresh).writeKeys, (scanDivisionCell ctx width).key ≠ key := by
  intro key member same
  rw [nativeScan_writeKeys_underWorkspace] at member
  apply ctx.canonicalFreshKey_fresh
  change ctx.canonicalFreshKey = key at same
  rw [same]
  exact nativeScan_writeKeys_subset_context cells member

/-- Popping the genuine workspace exposes the same pending cursor observations. -/
lemma nativeScan_pendingReads_popWorkspace
    (cells : ScanCells ctx modulusWidth (phaseBits + 1))
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addWorkspace key shape fresh))
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : PendingCursorReads (cells.underWorkspace key shape fresh) store cursor) :
    PendingCursorReads cells (Store.popWorkspace key shape fresh store) cursor := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat (Store.read_popWorkspace_underWorkspace
      key shape fresh store (cellRead cells.cursor.numerator))).trans reads.numerator
  · exact (congrArg CShape.Value.toNat (Store.read_popWorkspace_underWorkspace
      key shape fresh store (cellRead cells.cursor.denominator))).trans reads.denominator
  · exact (congrArg CShape.Value.toNat (Store.read_popWorkspace_underWorkspace
      key shape fresh store (cellRead cells.cursor.older))).trans reads.older
  · exact (congrArg CShape.Value.toNat (Store.read_popWorkspace_underWorkspace
      key shape fresh store (cellRead cells.cursor.previous))).trans reads.previous
  · exact (Store.read_popWorkspace_underWorkspace key shape fresh store
      (cellRead cells.cursor.active)).trans reads.active
  · exact (Store.read_popWorkspace_underWorkspace key shape fresh store
      (cellRead cells.accepted)).trans reads.accepted

/-- Popping the genuine workspace exposes the same selected word and frozen latches. -/
lemma nativeScan_chosenReads_popWorkspace
    (cells : ScanCells ctx modulusWidth (phaseBits + 1))
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addWorkspace key shape fresh)) (candidate : Nat)
    (reads : ChosenCursorReads (cells.underWorkspace key shape fresh) store candidate) :
    ChosenCursorReads cells (Store.popWorkspace key shape fresh store) candidate := by
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat (Store.read_popWorkspace_underWorkspace
      key shape fresh store (cellRead cells.selected))).trans reads.selected
  · exact (Store.read_popWorkspace_underWorkspace key shape fresh store
      (cellRead cells.accepted)).trans reads.accepted
  · exact (Store.read_popWorkspace_underWorkspace key shape fresh store
      (cellRead cells.cursor.active)).trans reads.inactive

/-- A complete actual active visit follows the source decision with fresh division facts proved. -/
lemma nativeScan_activeVisit_source_decision {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (pending : PendingCursorReads cells store cursor)
    (source : ScanSourceReads spec input base cells store)
    (fits : cursor.candidate.denominator < 2 ^ (phaseBits + 1)) :
    if ClassicalAlgorithms.OrderRecovery.validateCandidate spec input
        cursor.candidate.denominator then
      ChosenCursorReads cells (activeVisitStep (model := model) spec.modulusSpec base cells store).1
        cursor.candidate.denominator
    else
      PendingCursorReads cells
        (activeVisitStep (model := model) spec.modulusSpec base cells store).1
        cursor.advance := by
  let key := ctx.canonicalFreshKey
  let shape := cursorDivisionShape (phaseBits + 1)
  have fresh := ctx.canonicalFreshKey_fresh
  let lifted := cells.underWorkspace key shape fresh
  let entered := store.pushWorkspace key shape fresh
  have liftedBaseFree : ∀ written ∈ lifted.writeKeys,
      written ∉ (base.underWorkspace key shape fresh).storageKeys := by
    simpa only [lifted, nativeScan_writeKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
      using baseFree
  have actual := nativeScan_visit_source_decision (model := model) spec input
    (base.underWorkspace key shape fresh) lifted
    (nativeScan_separated_underWorkspace cells separated key shape fresh)
    (scanDivisionCell ctx (phaseBits + 1))
    (nativeScan_division_writeKeys_separate cells)
    (nativeScan_division_input_separate base)
    (nativeScan_division_input_separate cells.zero)
    (nativeScan_division_input_separate cells.one) liftedBaseFree entered cursor
    (nativeScan_pendingReads_underWorkspace cells store cursor pending key shape fresh)
    (nativeScan_sourceReads_underWorkspace spec input base cells store source key shape fresh) fits
  split
  · rename_i accepted
    rw [if_pos accepted] at actual
    exact nativeScan_chosenReads_popWorkspace cells key shape fresh _
      cursor.candidate.denominator actual
  · rename_i rejected
    rw [if_neg rejected] at actual
    exact nativeScan_pendingReads_popWorkspace cells key shape fresh _ cursor.advance actual

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
