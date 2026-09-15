/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.ActiveVisitState

/-!
# Actual activity-slot decisions of the source cursor

The real activity reference alone selects whether a visit runs. For a
represented pending source cursor, its nonzero denominator therefore selects
the verified active visit. All source base and constant reads survive that
same actual slot.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- A true actual activity read selects exactly the existing active-visit record. -/
theorem nativeScan_slot_active {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (store : Store ctx)
    (active : store.read (cellRead cells.cursor.active) = .bit true) :
    (scanSlotStep spec base cells store).1 = (activeVisitStep spec base cells store).1 := by
  change (activityChoiceStep spec base cells
    (store.read (cellRead cells.cursor.active)) store).1 = _
  exact congrArg (fun value => (activityChoiceStep spec base cells value store).1) active

/-- Each actual slot keeps the original represented base and the real comparison constants. -/
theorem nativeScan_slot_source_reads
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (store : Store ctx) (source : ScanSourceReads spec input base cells store) :
    ScanSourceReads spec input base cells (scanSlotStep spec.modulusSpec base cells store).1 :=
  nativeScan_iterate_source_reads spec input base cells separated baseFree store source 1

/-- An active source cursor takes the exact source decision through the actual activity slot. -/
theorem nativeScan_slot_source_decision
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (pending : PendingCursorReads cells store cursor)
    (source : ScanSourceReads spec input base cells store)
    (active : cursor.denominator ≠ 0)
    (fits : cursor.candidate.denominator < 2 ^ (phaseBits + 1)) :
    if ClassicalAlgorithms.OrderRecovery.validateCandidate spec input
        cursor.candidate.denominator then
      ChosenCursorReads cells (scanSlotStep spec.modulusSpec base cells store).1
        cursor.candidate.denominator
    else
      PendingCursorReads cells (scanSlotStep spec.modulusSpec base cells store).1
        cursor.advance := by
  have sourceActive :=
    (ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor.active_eq_true_iff
      cursor).mpr active
  have actualActive := pending.active.trans (congrArg CShape.Value.bit sourceActive)
  rw [nativeScan_slot_active spec.modulusSpec base cells store actualActive]
  exact nativeScan_activeVisit_source_decision spec input base cells separated baseFree store
    cursor pending source fits

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
