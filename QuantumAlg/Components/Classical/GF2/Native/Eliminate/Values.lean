/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Eliminate.Semantics
import all QuantumAlg.Util.Classical.GF2

/-!
# Original mathematical values of actual GF(2) row elimination

The actual matrix read determines the pure ordered samples. One native target
updates exactly its original row, and the real chronological target traversal
produces the original `eliminateRows` matrix. The pivot row is preserved while
later targets still read their original words. No valid-pivot, zero-workspace,
sample-independence or positive-width premise is needed for these equalities.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem nativeXor_value (left right : ClassicalAlgorithms.Word width) :
    CShape.wordBitXor width (.unsignedWord left) (.unsignedWord right) =
      .unsignedWord (ClassicalAlgorithms.GF2.rowXor left right) := by
  apply congrArg CShape.Value.unsignedWord
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow left.isLt right.isLt)

private theorem encodedRows_xor (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (pivot target : Fin rowCount) :
    CShape.vectorRowXor (.fixedVector (fun row => .unsignedWord (samples row))) pivot target =
      .fixedVector (fun row => .unsignedWord
        (Function.update samples target
          (ClassicalAlgorithms.GF2.rowXor (samples target) (samples pivot)) row)) := by
  apply congrArg CShape.Value.fixedVector
  funext row
  by_cases selected : row = target
  · subst row
    simpa only [Function.update_self, CShape.Value.get] using
      nativeXor_value (samples target) (samples pivot)
  · simp only [Function.update_of_ne selected, CShape.Value.get]

private theorem eliminateStep_update (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (pivot target : Fin rowCount) (column : Fin width) :
    ClassicalAlgorithms.GF2.eliminateStep pivot column samples target =
      Function.update samples target
        (ClassicalAlgorithms.GF2.eliminateRow pivot column samples target) := by
  by_cases same : target = pivot
  · simp [ClassicalAlgorithms.GF2.eliminateStep, ClassicalAlgorithms.GF2.eliminateRow, same]
  · by_cases active : ClassicalAlgorithms.GF2.testBit (samples target) column = true
    · simp [ClassicalAlgorithms.GF2.eliminateStep, ClassicalAlgorithms.GF2.eliminateRow,
        ClassicalAlgorithms.GF2.rowXorAt, same, active]
    · simp [ClassicalAlgorithms.GF2.eliminateStep, ClassicalAlgorithms.GF2.eliminateRow,
        same, active]

/-- The actual stored pivot-column test is the original pure MSB-first bit. -/
theorem gf2EliminationBit_of_rows
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (target : Fin rowCount) (column : Fin width) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (represented : store.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row))) :
    (store.read (eliminationBit matrix target column)).toBool =
      ClassicalAlgorithms.GF2.testBit (samples target) column := by
  rw [gf2EliminationBit_value, represented]
  exact (ClassicalAlgorithms.GF2.testBit_machine_coordinate (samples target) column).symm

/-- One actual target record writes precisely the original independent row update. -/
theorem gf2EliminateTarget_read_matrix
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (represented : store.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row))) :
    (eliminateTargetStep matrix pivot target column store).1.read
      (.storage matrix.toCStorageRef) =
        .fixedVector (fun row => .unsignedWord
          (Function.update samples target
            (ClassicalAlgorithms.GF2.eliminateRow pivot column samples target) row)) := by
  rw [← eliminateStep_update samples pivot target column, gf2EliminateTarget_store]
  by_cases same : target = pivot
  · simpa only [if_pos same, ClassicalAlgorithms.GF2.eliminateStep] using represented
  · rw [if_neg same, gf2EliminationBit_of_rows matrix target column store samples represented]
    by_cases active : ClassicalAlgorithms.GF2.testBit (samples target) column = true
    · rw [if_pos active, Store.read_write_same, represented]
      simpa only [ClassicalAlgorithms.GF2.eliminateStep, if_neg same, if_pos active,
        ClassicalAlgorithms.GF2.rowXorAt] using encodedRows_xor samples pivot target
    · simpa only [if_neg active, ClassicalAlgorithms.GF2.eliminateStep, if_neg same]
        using represented

private def eliminatedPrefix (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (pivot : Fin rowCount) (column : Fin width) (count : Nat) :
    ClassicalAlgorithms.GF2.Samples rowCount width :=
  fun row => if row.val < count then
    ClassicalAlgorithms.GF2.eliminateRow pivot column samples row else samples row

private theorem eliminatedPrefix_pivot
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (pivot : Fin rowCount) (column : Fin width) (count : Nat) :
    eliminatedPrefix samples pivot column count pivot = samples pivot := by
  simp [eliminatedPrefix, ClassicalAlgorithms.GF2.eliminateRow]

private theorem eliminatedPrefix_update
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (pivot target : Fin rowCount) (column : Fin width) :
    Function.update (eliminatedPrefix samples pivot column target.val) target
        (ClassicalAlgorithms.GF2.eliminateRow pivot column
          (eliminatedPrefix samples pivot column target.val) target) =
      eliminatedPrefix samples pivot column (target.val + 1) := by
  funext row
  by_cases selected : row = target
  · subst row
    rw [Function.update_self]
    have targetValue : eliminatedPrefix samples pivot column target.val target =
        samples target := by simp [eliminatedPrefix]
    have pivotValue := eliminatedPrefix_pivot samples pivot column target.val
    calc
      ClassicalAlgorithms.GF2.eliminateRow pivot column
          (eliminatedPrefix samples pivot column target.val) target =
          ClassicalAlgorithms.GF2.eliminateRow pivot column samples target := by
        unfold ClassicalAlgorithms.GF2.eliminateRow
        rw [targetValue, pivotValue]
      _ = eliminatedPrefix samples pivot column (target.val + 1) target := by
        simp only [eliminatedPrefix, Nat.lt_succ_self, if_true]
  · rw [Function.update_of_ne selected]
    unfold eliminatedPrefix
    have same : row.val < target.val ↔ row.val < target.val + 1 := by
      constructor
      · omega
      · intro before
        have unequal : row.val ≠ target.val := fun equal => selected (Fin.ext equal)
        omega
    simp only [same]

/-- The actual chronological target traversal returns exactly the original elimination matrix. -/
theorem gf2EliminateWithPivot_read_matrix
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (represented : store.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row))) :
    (eliminateWithPivotStep matrix pivot column store).1.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord
        (ClassicalAlgorithms.GF2.eliminateRows samples pivot column row)) := by
  let invariant (count : Nat) (current : Store ctx) : Prop :=
    current.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (eliminatedPrefix samples pivot column count row))
  have initial : invariant 0 store := by simpa [invariant, eliminatedPrefix] using represented
  have advance : ∀ (target : Fin rowCount) (current : Store ctx),
      invariant target.val current →
        invariant (target.val + 1) (eliminateTargetStep matrix pivot target column current).1 := by
    intro target current established
    have actual := gf2EliminateTarget_read_matrix matrix pivot target column current
      (eliminatedPrefix samples pivot column target.val) established
    rw [eliminatedPrefix_update] at actual
    exact actual
  have completed := Circuit.forRangeRecord_invariant rowCount
    (fun target => eliminateTarget matrix pivot target column)
    (fun target => eliminateTargetStep matrix pivot target column)
    invariant advance store initial
  change invariant rowCount (eliminateWithPivotStep matrix pivot column store).1 at completed
  have final : eliminatedPrefix samples pivot column rowCount =
      ClassicalAlgorithms.GF2.eliminateRows samples pivot column := by
    funext row
    simp only [eliminatedPrefix, row.isLt, if_true, ClassicalAlgorithms.GF2.eliminateRows]
  change (eliminateWithPivotStep matrix pivot column store).1.read (.storage matrix.toCStorageRef)
    = CShape.Value.fixedVector (fun row => CShape.Value.unsignedWord
      (eliminatedPrefix samples pivot column rowCount row)) at completed
  rw [final] at completed
  exact completed

end

end QuantumAlg.ClassicalRoutines.GF2.Native
