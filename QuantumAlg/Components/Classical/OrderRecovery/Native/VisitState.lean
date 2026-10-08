/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.SelectionState

/-!
# The complete actual visit follows the source candidate decision

This combines the real division and continuant, the real modular validation,
and the branch selected by its stored bit. A source-accepted candidate is
copied and freezes the scan; a rejected candidate advances the same source
cursor using the retained remainder. All observations refer to the existing
complete visit record.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth phaseBits : Nat}

/-- One complete real visit follows exactly the source decision for its materialized candidate. -/
theorem nativeScan_visit_source_decision
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (division : CWriteRef ctx (cursorDivisionShape (phaseBits + 1)))
    (divisionFree : ∀ key ∈ cells.writeKeys, division.key ≠ key)
    (divisionBase : division.key ∉ base.storageKeys)
    (divisionZero : division.key ∉ cells.zero.storageKeys)
    (divisionOne : division.key ∉ cells.one.storageKeys)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (pending : PendingCursorReads cells store cursor)
    (source : ScanSourceReads spec input base cells store)
    (fits : cursor.candidate.denominator < 2 ^ (phaseBits + 1)) :
    if ClassicalAlgorithms.OrderRecovery.validateCandidate spec input
        cursor.candidate.denominator then
      ChosenCursorReads cells
        (visitWithDivisionStep (model := model) spec.modulusSpec base cells division store).1
        cursor.candidate.denominator
    else
      PendingCursorReads cells
        (visitWithDivisionStep (model := model) spec.modulusSpec base cells division store).1
        cursor.advance := by
  let materialized := candidateState (model := model) cells division store
  let validated := (validateStep (model := model) spec.modulusSpec base
    (cellRead cells.cursor.candidate)
    cells.zero cells.one cells.power cells.positive cells.valid materialized).1
  have candidateAtPrefix := nativeScan_candidateState_candidate (model := model)
    cells division divisionFree
    store cursor pending.toCursorReads fits
  have cursorAtPrefix := nativeScan_candidateState_cursor (model := model)
    cells separated division divisionFree
    store cursor pending.toCursorReads
  have sourceAtPrefix := nativeScan_candidateState_source (model := model)
    spec input base cells separated division
    divisionBase divisionZero divisionOne (baseFree _ (by simp [ScanCells.writeKeys])) store source
  have validValue : validated.read (cellRead cells.valid) =
      .bit (ClassicalAlgorithms.OrderRecovery.validateCandidate spec input
        cursor.candidate.denominator) :=
    nativeScan_validation_matches_source spec input base cells separated materialized
      cursor.candidate.denominator fits sourceAtPrefix.baseValue candidateAtPrefix
      sourceAtPrefix.zeroValue sourceAtPrefix.oneValue
  have candidateAtValidation : (validated.read (cellRead cells.cursor.candidate)).toNat =
      cursor.candidate.denominator :=
    (congrArg CShape.Value.toNat
      (nativeScan_validation_candidate spec.modulusSpec base cells separated materialized)).trans
        candidateAtPrefix
  have cursorAtValidation : CursorReads cells.cursor validated cursor :=
    nativeScan_validation_cursor spec.modulusSpec base cells separated materialized cursor
      cursorAtPrefix
  have sourceAtValidation : ScanSourceReads spec input base cells validated :=
    nativeScan_validation_source spec input base cells separated baseFree
      materialized sourceAtPrefix
  have candidateDivision : cells.cursor.candidate.key ≠ division.key :=
    (divisionFree _ (by simp [ScanCells.writeKeys])).symm
  have remainderAtValidation : (validated.read (.second (cellRead division))).toNat =
      cursor.remainder :=
    (congrArg (fun value => value.second.toNat)
      (nativeScan_validation_division spec.modulusSpec base cells division divisionFree
        materialized)).trans
          (nativeScan_candidateState_remainder cells division candidateDivision store cursor
            pending.toCursorReads)
  have acceptedAtPrefix : materialized.read (cellRead cells.accepted) = .bit false :=
    (nativeScan_candidateState_read_other cells division (cellRead cells.accepted)
      (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 4 7 (by decide)
        (List.mem_singleton.mp present)) store).trans pending.accepted
  have acceptedAtValidation : validated.read (cellRead cells.accepted) = .bit false :=
    (nativeValidation_read_other spec.modulusSpec base (cellRead cells.cursor.candidate)
      cells.zero cells.one cells.power cells.positive cells.valid (cellRead cells.accepted)
      (fun present => nativeScan_separated_keys cells separated 8 7 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 9 7 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 10 7 (by decide)
        (List.mem_singleton.mp present)) materialized).trans acceptedAtPrefix
  have selectedStore :
      (visitWithDivisionStep (model := model) spec.modulusSpec base cells division store).1 =
        (selectionChoiceStep (model := model) cells (.second (cellRead division))
          (.bit (ClassicalAlgorithms.OrderRecovery.validateCandidate spec input
            cursor.candidate.denominator)) validated).1 :=
    congrArg (fun value => (selectionChoiceStep (model := model) cells
      (.second (cellRead division)) value
      validated).1) validValue
  cases choice : ClassicalAlgorithms.OrderRecovery.validateCandidate spec input
      cursor.candidate.denominator with
  | false =>
      change PendingCursorReads cells
        (visitWithDivisionStep (model := model) spec.modulusSpec base cells division store).1
        cursor.advance
      rw [choice] at selectedStore
      rw [selectedStore]
      apply nativeScan_advance_pending cells separated (.second (cellRead division))
        ?_ validated cursor cursorAtValidation candidateAtValidation remainderAtValidation
        sourceAtValidation.zeroValue acceptedAtValidation
      intro key member
      have persistent : key ∈ cells.writeKeys := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [ScanCells.writeKeys]
      exact fun present => divisionFree key persistent (List.mem_singleton.mp present).symm
  | true =>
      change ChosenCursorReads cells
        (visitWithDivisionStep (model := model) spec.modulusSpec base cells division store).1
        cursor.candidate.denominator
      rw [choice] at selectedStore validValue
      rw [selectedStore]
      exact nativeScan_accept_chosen cells separated validated cursor.candidate.denominator
        candidateAtValidation validValue

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
