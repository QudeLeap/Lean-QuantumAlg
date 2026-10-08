/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan.Iteration
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Validation.Laws
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Acceptance

/-!
# Exact structural read frames through the finite recovery scan

Only the actual cursor, selected result and validation destinations can
change. Each division pair is a genuine fresh lexical head. All original
reads outside the real scan destinations survive active visits, inactive
slots and the complete fixed-fuel execution with their exact values.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {modulusWidth candidateWidth : Nat}

/-- The actual persistent destinations written by either real scan branch. -/
def ScanCells.writeKeys {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (cells : ScanCells ctx modulusWidth candidateWidth) : List StorageKey :=
  [cells.cursor.older.key, cells.cursor.previous.key, cells.cursor.numerator.key,
    cells.cursor.denominator.key, cells.cursor.candidate.key, cells.cursor.active.key,
    cells.selected.key, cells.accepted.key, cells.power.key, cells.positive.key, cells.valid.key]

/-- Lifting the real scan destinations through a workspace preserves their exact keys. -/
theorem nativeScan_writeKeys_underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (cells.underWorkspace key shape fresh).writeKeys = cells.writeKeys := by
  rfl

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem selection_read_other (cells : ScanCells ctx modulusWidth candidateWidth)
    (remainder : CInputRef ctx (.unsignedWord candidateWidth)) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ cells.writeKeys, key ∉ other.storageKeys) (store : Store ctx) :
    (selectionChoiceStep (model := model) cells remainder value store).1.read other =
      store.read other := by
  cases value with
  | bit value =>
      cases value
      · apply nativeCursor_advance_read_other cells.cursor remainder cells.zero other
        intro key member
        apply separate key
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [ScanCells.writeKeys]
      · exact nativeCursor_accept_read_other (cellRead cells.cursor.candidate)
          (cellRead cells.valid) cells.selected cells.accepted cells.cursor.active other
          (separate _ (by simp [ScanCells.writeKeys]))
          (separate _ (by simp [ScanCells.writeKeys]))
          (separate _ (by simp [ScanCells.writeKeys])) store

/-- The full actual visit preserves every read outside its division pair and persistent writes. -/
theorem nativeScan_visit_read_other (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (division : CWriteRef ctx (cursorDivisionShape candidateWidth))
    {shape : CShape} (other : CInputRef ctx shape)
    (divisionFree : division.key ∉ other.storageKeys)
    (separate : ∀ key ∈ cells.writeKeys, key ∉ other.storageKeys) (store : Store ctx) :
    (visitWithDivisionStep (model := model) spec base cells division store).1.read other =
      store.read other := by
  unfold visitWithDivisionStep
  rw [selection_read_other cells _ _ other separate]
  rw [nativeValidation_read_other spec base (cellRead cells.cursor.candidate) cells.zero cells.one
    cells.power cells.positive cells.valid other
    (separate _ (by simp [ScanCells.writeKeys]))
    (separate _ (by simp [ScanCells.writeKeys]))
    (separate _ (by simp [ScanCells.writeKeys]))]
  exact nativeCandidatePrefix_read_other (cellRead cells.cursor.numerator)
    (cellRead cells.cursor.denominator) (cellRead cells.cursor.previous)
    (cellRead cells.cursor.older) division cells.cursor.candidate other divisionFree
    (separate _ (by simp [ScanCells.writeKeys])) store

/-- The genuine fresh division pair is separate from every original structural read. -/
theorem nativeScan_division_input_separate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape}
    (other : CInputRef ctx shape) :
    (scanDivisionCell ctx candidateWidth).key ∉
      (other.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
        ctx.canonicalFreshKey_fresh).storageKeys := by
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)

/-- Allocating and releasing the actual division pair preserves every external scan read. -/
theorem nativeScan_activeVisit_read_other (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) {shape : CShape}
    (other : CInputRef ctx shape)
    (separate : ∀ key ∈ cells.writeKeys, key ∉ other.storageKeys) (store : Store ctx) :
    (activeVisitStep (model := model) spec base cells store).1.read other =
      store.read other := by
  have liftedSeparate : ∀ key ∈
      (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
        ctx.canonicalFreshKey_fresh).writeKeys,
      key ∉ (other.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
        ctx.canonicalFreshKey_fresh).storageKeys := by
    simpa only [nativeScan_writeKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
      using separate
  unfold activeVisitStep
  rw [Store.read_popWorkspace_underWorkspace]
  rw [nativeScan_visit_read_other spec _ _ _ _ (nativeScan_division_input_separate other)
    liftedSeparate]
  exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other

private theorem activity_read_other (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ cells.writeKeys, key ∉ other.storageKeys) (store : Store ctx) :
    (activityChoiceStep (model := model) spec base cells value store).1.read other =
      store.read other := by
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact nativeScan_activeVisit_read_other spec base cells other separate store

/-- The actual activity-gated slot preserves the same original structural reads. -/
theorem nativeScan_slot_read_other (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) {shape : CShape}
    (other : CInputRef ctx shape)
    (separate : ∀ key ∈ cells.writeKeys, key ∉ other.storageKeys) (store : Store ctx) :
    (scanSlotStep (model := model) spec base cells store).1.read other = store.read other :=
  activity_read_other spec base cells (store.read (cellRead cells.cursor.active))
    other separate store

/-- Every finite number of actual scan slots preserves the same exact external values. -/
theorem nativeScan_iterate_read_other (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (fuel : Nat) {shape : CShape}
    (other : CInputRef ctx shape)
    (separate : ∀ key ∈ cells.writeKeys, key ∉ other.storageKeys) (store : Store ctx) :
    ((fun initial => (scanSlotStep (model := model) spec base cells initial).1)^[fuel]
      store).read other =
      store.read other := by
  induction fuel generalizing store with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply, ih,
        nativeScan_slot_read_other spec base cells other separate]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
