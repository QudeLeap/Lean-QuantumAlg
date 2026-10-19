/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Semantics

/-!
# Remainder rotation and activity after both actual coefficient updates

The computed division pair remains live through the two coefficient updates.
The final two copies consume that same pair; no second division or uncharged
operation is introduced. Caller-read separation preserves the zero sentinel.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual body rotates total remainders and refreshes activity against the fresh zero cell. -/
lemma xgcdNativeActiveBody_remainder_values
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (scratch : Cells ctx (activeScratchShapes width)) (scratchDistinct : scratch.Distinct)
    (cross : CrossSeparated cells scratch) (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys)
    (scratchZero : ∀ index : Fin 4, (cellAt scratch index).ref.key ∉ zero.storageKeys)
    (store : Store ctx) :
    let final := activeBodyStore cells scratch zero store
    (final.read (GCD.cellRead (firstCell cells))).toNat =
        (store.read (GCD.cellRead (secondCell cells))).toNat %
          (store.read (GCD.cellRead (firstCell cells))).toNat ∧
      final.read (GCD.cellRead (secondCell cells)) =
        store.read (GCD.cellRead (firstCell cells)) ∧
      (final.read (GCD.cellRead (activeCell cells))).toBool =
        decide ((store.read (GCD.cellRead (secondCell cells))).toNat %
          (store.read (GCD.cellRead (firstCell cells))).toNat ≠ (store.read zero).toNat) ∧
      final.read zero = store.read zero := by
  let divided := store.applyOp
    (GCD.divisionOp (firstCell cells) (secondCell cells) (activeDivisionCell scratch))
  let widened := divided.applyOp (activeResizeQuotientOp scratch)
  let left := coefficientUpdateStore (coefficientRead (activeQuotientCell scratch))
    (firstLeftCell cells) (secondLeftCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch) widened
  let right := coefficientUpdateStore (coefficientRead (activeQuotientCell scratch))
    (firstRightCell cells) (secondRightCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch) left
  let rotated := right.applyOp (GCD.rotateSecondOp (firstCell cells) (secondCell cells))
  let reduced := rotated.applyOp
    (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch))
  let tested := reduced.applyOp (GCD.testActiveOp (firstCell cells) zero (activeCell cells))
  have coefficientsPreserve {shape : CShape} (cell : CWriteRef ctx shape)
      (firstLeft : (firstLeftCell cells).key ≠ cell.key)
      (secondLeft : (secondLeftCell cells).key ≠ cell.key)
      (firstRight : (firstRightCell cells).key ≠ cell.key)
      (secondRight : (secondRightCell cells).key ≠ cell.key)
      (product : (activeProductCell scratch).key ≠ cell.key)
      (updated : (activeUpdatedCell scratch).key ≠ cell.key) :
      right.read (GCD.cellRead cell) = widened.read (GCD.cellRead cell) := by
    exact (coefficient_preserves_cell _ _ _ _ _ cell
      firstRight secondRight product updated left).trans
      (coefficient_preserves_cell _ _ _ _ _ cell firstLeft secondLeft product updated widened)
  have rightFirst : right.read (GCD.cellRead (firstCell cells)) =
      store.read (GCD.cellRead (firstCell cells)) := by
    rw [coefficientsPreserve (firstCell cells)
      (state_ne cells distinct 2 0 (by decide)) (state_ne cells distinct 4 0 (by decide))
      (state_ne cells distinct 3 0 (by decide)) (state_ne cells distinct 5 0 (by decide))
      (cross_ne cells scratch cross 0 2).symm (cross_ne cells scratch cross 0 3).symm]
    change (divided.applyOp (activeResizeQuotientOp scratch)).read _ = _
    rw [GCD.op_preserves_cell (activeResizeQuotientOp scratch) (firstCell cells)
      (cross_ne cells scratch cross 0 1).symm]
    exact GCD.op_preserves_cell
      (GCD.divisionOp (firstCell cells) (secondCell cells) (activeDivisionCell scratch))
      (firstCell cells)
      (cross_ne cells scratch cross 0 0).symm store
  have rightDivision : right.read (GCD.cellRead (activeDivisionCell scratch)) =
      divided.read (GCD.cellRead (activeDivisionCell scratch)) := by
    rw [coefficientsPreserve (activeDivisionCell scratch)
      (cross_ne cells scratch cross 2 0) (cross_ne cells scratch cross 4 0)
      (cross_ne cells scratch cross 3 0) (cross_ne cells scratch cross 5 0)
      (scratch_ne scratch scratchDistinct 2 0 (by decide))
      (scratch_ne scratch scratchDistinct 3 0 (by decide))]
    exact GCD.op_preserves_cell (activeResizeQuotientOp scratch) (activeDivisionCell scratch)
      (scratch_ne scratch scratchDistinct 1 0 (by decide)) divided
  have rotatedDivision : rotated.read (GCD.cellRead (activeDivisionCell scratch)) =
      divided.read (GCD.cellRead (activeDivisionCell scratch)) := by
    exact (GCD.op_preserves_cell (GCD.rotateSecondOp (firstCell cells) (secondCell cells))
      (activeDivisionCell scratch)
      (cross_ne cells scratch cross 1 0) right).trans rightDivision
  have reducedFirst : (reduced.read (GCD.cellRead (firstCell cells))).toNat =
      (store.read (GCD.cellRead (secondCell cells))).toNat %
        (store.read (GCD.cellRead (firstCell cells))).toNat := by
    rw [GCD.remainder_read, rotatedDivision, GCD.division_read]
    exact GCD.gcdOperands_divRem_remainder _ _
  have reducedSecond : reduced.read (GCD.cellRead (secondCell cells)) =
      store.read (GCD.cellRead (firstCell cells)) := by
    rw [GCD.op_preserves_cell
        (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch)) (secondCell cells)
        (state_ne cells distinct 0 1 (by decide)),
      GCD.rotate_read, rightFirst]
  have rightZero : right.read zero = store.read zero := by
    change (coefficientUpdateStore _ _ _ _ _ (coefficientUpdateStore _ _ _ _ _
      ((store.applyOp _).applyOp _))).read zero = _
    rw [xgcdCoefficientUpdate_read_other (coefficientRead (activeQuotientCell scratch))
        (firstRightCell cells) (secondRightCell cells)
        (activeProductCell scratch) (activeUpdatedCell scratch) zero
        (stateZero 3) (stateZero 5) (scratchZero 2) (scratchZero 3),
      xgcdCoefficientUpdate_read_other (coefficientRead (activeQuotientCell scratch))
        (firstLeftCell cells) (secondLeftCell cells)
        (activeProductCell scratch) (activeUpdatedCell scratch) zero
        (stateZero 2) (stateZero 4) (scratchZero 2) (scratchZero 3),
      Store.read_applyOp_of_not_mem_storageKeys _ (activeResizeQuotientOp scratch)
        zero (scratchZero 1),
      Store.read_applyOp_of_not_mem_storageKeys _
        (GCD.divisionOp (firstCell cells) (secondCell cells) (activeDivisionCell scratch))
        zero (scratchZero 0)]
  have reducedZero : reduced.read zero = store.read zero := by
    change ((right.applyOp (GCD.rotateSecondOp (firstCell cells) (secondCell cells))).applyOp
      (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch))).read zero = _
    rw [Store.read_applyOp_of_not_mem_storageKeys _
        (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch)) zero (stateZero 0),
      Store.read_applyOp_of_not_mem_storageKeys _
        (GCD.rotateSecondOp (firstCell cells) (secondCell cells)) zero (stateZero 1), rightZero]
  dsimp only
  refine ⟨?_, ?_, ?_, xgcdNativeActiveBody_read_other cells scratch zero zero
    stateZero scratchZero store⟩
  · change ((tested.applyOp (GCD.negateActiveOp (activeCell cells))).read
      (GCD.cellRead (firstCell cells))).toNat = _
    rw [GCD.op_preserves_cell (GCD.negateActiveOp (activeCell cells)) (firstCell cells)
        (state_ne cells distinct 6 0 (by decide)),
      GCD.op_preserves_cell (GCD.testActiveOp (firstCell cells) zero (activeCell cells))
        (firstCell cells) (state_ne cells distinct 6 0 (by decide))]
    exact reducedFirst
  · change (tested.applyOp (GCD.negateActiveOp (activeCell cells))).read
      (GCD.cellRead (secondCell cells)) = _
    rw [GCD.op_preserves_cell (GCD.negateActiveOp (activeCell cells)) (secondCell cells)
        (state_ne cells distinct 6 1 (by decide)),
      GCD.op_preserves_cell (GCD.testActiveOp (firstCell cells) zero (activeCell cells))
        (secondCell cells) (state_ne cells distinct 6 1 (by decide))]
    exact reducedSecond
  · change ((tested.applyOp (GCD.negateActiveOp (activeCell cells))).read
      (GCD.cellRead (activeCell cells))).toBool = _
    rw [GCD.negate_read, GCD.test_read, reducedFirst, reducedZero]
    simp only [decide_not]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
