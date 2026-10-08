/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Candidate.State

/-!
# Source observations through actual candidate validation

The real modular-power output and two validation latches are the only
persistent writes. The actual candidate, Euclidean cursor and division pair
survive that validation, as do the source base and both comparison constants.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth phaseBits : Nat}

/-- Validation preserves the four actual source cursor coordinates. -/
theorem nativeScan_validation_cursor {width : Nat}
    (spec : ModulusSpec modulusWidth) (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (separated : cells.Separated) (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : CursorReads cells.cursor store cursor) :
    CursorReads cells.cursor
      (validateStep (model := model) spec base (cellRead cells.cursor.candidate)
        cells.zero cells.one
        cells.power cells.positive cells.valid store).1 cursor := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat (nativeValidation_read_other spec base
      (cellRead cells.cursor.candidate) cells.zero cells.one cells.power cells.positive cells.valid
      (cellRead cells.cursor.numerator)
      (fun present => nativeScan_separated_keys cells separated 8 2 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 9 2 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 10 2 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.numerator
  · exact (congrArg CShape.Value.toNat (nativeValidation_read_other spec base
      (cellRead cells.cursor.candidate) cells.zero cells.one cells.power cells.positive cells.valid
      (cellRead cells.cursor.denominator)
      (fun present => nativeScan_separated_keys cells separated 8 3 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 9 3 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 10 3 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.denominator
  · exact (congrArg CShape.Value.toNat (nativeValidation_read_other spec base
      (cellRead cells.cursor.candidate) cells.zero cells.one cells.power cells.positive cells.valid
      (cellRead cells.cursor.older)
      (fun present => nativeScan_separated_keys cells separated 8 0 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 9 0 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 10 0 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.older
  · exact (congrArg CShape.Value.toNat (nativeValidation_read_other spec base
      (cellRead cells.cursor.candidate) cells.zero cells.one cells.power cells.positive cells.valid
      (cellRead cells.cursor.previous)
      (fun present => nativeScan_separated_keys cells separated 8 1 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 9 1 (by decide)
        (List.mem_singleton.mp present))
      (fun present => nativeScan_separated_keys cells separated 10 1 (by decide)
        (List.mem_singleton.mp present)) store)).trans reads.previous

/-- The already materialized candidate survives the actual modular validation unchanged. -/
theorem nativeScan_validation_candidate {width : Nat}
    (spec : ModulusSpec modulusWidth) (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (separated : cells.Separated) (store : Store ctx) :
    (validateStep (model := model) spec base (cellRead cells.cursor.candidate)
        cells.zero cells.one
      cells.power cells.positive cells.valid store).1.read (cellRead cells.cursor.candidate) =
        store.read (cellRead cells.cursor.candidate) :=
  nativeValidation_read_other spec base (cellRead cells.cursor.candidate) cells.zero cells.one
    cells.power cells.positive cells.valid (cellRead cells.cursor.candidate)
    (fun present => nativeScan_separated_keys cells separated 8 4 (by decide)
      (List.mem_singleton.mp present))
    (fun present => nativeScan_separated_keys cells separated 9 4 (by decide)
      (List.mem_singleton.mp present))
    (fun present => nativeScan_separated_keys cells separated 10 4 (by decide)
      (List.mem_singleton.mp present)) store

/-- The same retained quotient and remainder remain available to the actual branch update. -/
theorem nativeScan_validation_division {width : Nat}
    (spec : ModulusSpec modulusWidth) (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (cursorDivisionShape width))
    (divisionFree : ∀ key ∈ cells.writeKeys, division.key ≠ key) (store : Store ctx) :
    (validateStep (model := model) spec base (cellRead cells.cursor.candidate)
        cells.zero cells.one
      cells.power cells.positive cells.valid store).1.read (cellRead division) =
        store.read (cellRead division) :=
  nativeValidation_read_other spec base (cellRead cells.cursor.candidate) cells.zero cells.one
    cells.power cells.positive cells.valid (cellRead division)
    (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
      (List.mem_singleton.mp present).symm)
    (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
      (List.mem_singleton.mp present).symm)
    (fun present => divisionFree _ (by simp [ScanCells.writeKeys])
      (List.mem_singleton.mp present).symm) store

/-- The original source base and comparison operands survive the actual validation. -/
theorem nativeScan_validation_source
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (store : Store ctx) (reads : ScanSourceReads spec input base cells store) :
    ScanSourceReads spec input base cells
      (validateStep (model := model) spec.modulusSpec base (cellRead cells.cursor.candidate)
        cells.zero cells.one
        cells.power cells.positive cells.valid store).1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (nativeValidation_read_other spec.modulusSpec base (cellRead cells.cursor.candidate)
      cells.zero cells.one cells.power cells.positive cells.valid base
      (baseFree _ (by simp [ScanCells.writeKeys]))
      (baseFree _ (by simp [ScanCells.writeKeys]))
      (baseFree _ (by simp [ScanCells.writeKeys])) store).trans reads.baseValue
  · exact (congrArg CShape.Value.toNat (nativeValidation_read_other spec.modulusSpec base
      (cellRead cells.cursor.candidate) cells.zero cells.one cells.power cells.positive cells.valid
      cells.zero (separated.zeroFree _ (by simp [ScanCells.writeKeys]))
      (separated.zeroFree _ (by simp [ScanCells.writeKeys]))
      (separated.zeroFree _ (by simp [ScanCells.writeKeys])) store)).trans reads.zeroValue
  · exact (congrArg CShape.Value.toNat (nativeValidation_read_other spec.modulusSpec base
      (cellRead cells.cursor.candidate) cells.zero cells.one cells.power cells.positive cells.valid
      cells.one (separated.oneFree _ (by simp [ScanCells.writeKeys]))
      (separated.oneFree _ (by simp [ScanCells.writeKeys]))
      (separated.oneFree _ (by simp [ScanCells.writeKeys])) store)).trans reads.oneValue

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
