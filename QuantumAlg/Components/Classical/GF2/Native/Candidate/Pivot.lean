/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Values
import all QuantumAlg.Components.Classical.GF2.Native.Eliminate.Values

/-!
# Actual pivot-record selection of GF(2) candidate contributions

The original MSB-first stored row-record bit decides whether the real scoped
row contribution runs. The value and caller-frame equations below use that
actual bit and the original chronological store, without a valid-pivot or
zero-source promise. Canonical pivot records are related to their original
pure first-match lookup separately.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The original outer pivot-record branch preserves all reads outside its candidate word. -/
theorem gf2CandidatePivotRow_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) :
    (candidatePivotRowStep matrix rows free candidate zero row column store).1.read other =
      store.read other := by
  change (candidatePivotChoiceStep matrix free candidate zero row column
    (store.read (eliminationBit rows column row)) store).1.read other = _
  cases store.read (eliminationBit rows column row) with
  | bit value =>
      cases value
      · rfl
      · exact gf2CandidateRowSelected_read_other matrix free candidate zero row column
          store other separate

/-- The original stored pivot bit and real row intersection determine the candidate update. -/
theorem gf2CandidatePivotRow_candidate
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    ((candidatePivotRowStep matrix rows free candidate zero row column store).1.read
      (.storage candidate.toCStorageRef)).toNat =
      if (store.read (eliminationBit rows column row)).toBool then
        if (CShape.wordBitAnd width ((store.read (.storage matrix.toCStorageRef)).get row)
            (store.read (.storage free.toCStorageRef))).toNat =
              (store.read (.storage zero.toCStorageRef)).toNat then
          (store.read (.storage candidate.toCStorageRef)).toNat else
          (store.read (.storage candidate.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val
      else (store.read (.storage candidate.toCStorageRef)).toNat := by
  change ((candidatePivotChoiceStep matrix free candidate zero row column
    (store.read (eliminationBit rows column row)) store).1.read _).toNat = _
  cases store.read (eliminationBit rows column row) with
  | bit value =>
      cases value
      · rfl
      · exact gf2CandidateRowSelected_candidate matrix free candidate zero row column store

omit [BitWord.Selected model] in
/-- A canonical recorded pivot row reads exactly its original first-match row decision. -/
theorem gf2CandidatePivotBit_of_record
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (store : Store ctx)
    (represented : store.read (.storage rows.toCStorageRef) =
      .fixedVector (fun column => match ClassicalAlgorithms.GF2.pivotForColumn? result column with
        | none => CShape.wordOfNat rowCount 0
        | some pivot => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
            (fun row => decide (row = pivot.row)))))
    (row : Fin rowCount) (column : Fin width) :
    (store.read (eliminationBit rows column row)).toBool =
      match ClassicalAlgorithms.GF2.pivotForColumn? result column with
      | none => false
      | some pivot => decide (row = pivot.row) := by
  rw [gf2EliminationBit_value, represented]
  cases lookup : ClassicalAlgorithms.GF2.pivotForColumn? result column with
  | none =>
      simp only [lookup, CShape.Value.get, CShape.wordOfNat, CShape.Value.toNat,
        Nat.zero_mod, Nat.zero_testBit]
  | some pivot =>
      have bit := ClassicalAlgorithms.GF2.testBit_wordOfLogicalBits
        (fun current => decide (current = pivot.row)) row
      have coordinate := ClassicalAlgorithms.GF2.testBit_machine_coordinate
        (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun current => decide (current = pivot.row))) row
      simpa only [lookup, CShape.Value.get, CShape.Value.toNat] using
        coordinate.symm.trans bit

end

end QuantumAlg.ClassicalRoutines.GF2.Native
