/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Initialization.State
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package

/-!
# Actual word arithmetic of the extended-Euclidean active body

Separation describes the two actual live packages and is supplied by nested
lexical allocation. All scratch contents are arbitrary. The quotient is
computed before both coefficient updates; both updates use the same scratch
pair before remainder rotation. No activity or nonzero-divisor hypothesis is
needed for the total body arithmetic.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma state_ne (cells : Cells ctx (stateShapes width))
    (distinct : cells.Distinct) (left right : Fin 7) (different : left ≠ right) :
    stateKey cells left ≠ stateKey cells right :=
  fun same => different (xgcdNativeState_key_injective cells distinct same)

private lemma scratch_ne (scratch : Cells ctx (activeScratchShapes width))
    (distinct : scratch.Distinct) (left right : Fin 4) (different : left ≠ right) :
    (cellAt scratch left).ref.key ≠ (cellAt scratch right).ref.key := by
  exact fun same => different (workspaceCells_cellAt_key_injective scratch distinct same)

private lemma cross_ne (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width)) (cross : CrossSeparated cells scratch)
    (left : Fin 7) (right : Fin 4) :
    stateKey cells left ≠ (cellAt scratch right).ref.key := cross.keysNe left right

private lemma coefficient_preserves_cell {shape : CShape}
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (other : CWriteRef ctx shape)
    (firstFree : first.key ≠ other.key) (secondFree : second.key ≠ other.key)
    (productFree : product.key ≠ other.key) (updatedFree : updated.key ≠ other.key)
    (store : Store ctx) :
    (coefficientUpdateStore quotient first second product updated store).read (GCD.cellRead other) =
      store.read (GCD.cellRead other) := by
  apply xgcdCoefficientUpdate_read_other
  · simpa only [GCD.cellRead, CInputRef.storageKeys, List.mem_singleton] using firstFree
  · simpa only [GCD.cellRead, CInputRef.storageKeys, List.mem_singleton] using secondFree
  · simpa only [GCD.cellRead, CInputRef.storageKeys, List.mem_singleton] using productFree
  · simpa only [GCD.cellRead, CInputRef.storageKeys, List.mem_singleton] using updatedFree

/-- Every caller read outside both actual packages survives the full fourteen-operation body. -/
lemma xgcdNativeActiveBody_read_other (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape)
    (stateFree : ∀ index : Fin 7, stateKey cells index ∉ other.storageKeys)
    (scratchFree : ∀ index : Fin 4, (cellAt scratch index).ref.key ∉ other.storageKeys)
    (store : Store ctx) :
    (activeBodyStore cells scratch zero store).read other = store.read other := by
  unfold activeBodyStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (GCD.negateActiveOp (activeCell cells))
      other (stateFree 6),
    Store.read_applyOp_of_not_mem_storageKeys _
      (GCD.testActiveOp (firstCell cells) zero (activeCell cells)) other (stateFree 6),
    Store.read_applyOp_of_not_mem_storageKeys _
      (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch)) other (stateFree 0),
    Store.read_applyOp_of_not_mem_storageKeys _
      (GCD.rotateSecondOp (firstCell cells) (secondCell cells)) other (stateFree 1),
    xgcdCoefficientUpdate_read_other (coefficientRead (activeQuotientCell scratch))
      (firstRightCell cells) (secondRightCell cells)
      (activeProductCell scratch) (activeUpdatedCell scratch) other
      (stateFree 3) (stateFree 5) (scratchFree 2) (scratchFree 3),
    xgcdCoefficientUpdate_read_other (coefficientRead (activeQuotientCell scratch))
      (firstLeftCell cells) (secondLeftCell cells)
      (activeProductCell scratch) (activeUpdatedCell scratch) other
      (stateFree 2) (stateFree 4) (scratchFree 2) (scratchFree 3),
    Store.read_applyOp_of_not_mem_storageKeys _ (activeResizeQuotientOp scratch)
      other (scratchFree 1),
    Store.read_applyOp_of_not_mem_storageKeys _
      (GCD.divisionOp (firstCell cells) (secondCell cells) (activeDivisionCell scratch))
      other (scratchFree 0)]

/-- Literal modular word operations in both coefficient pairs, with the actual resized quotient. -/
lemma xgcdNativeActiveBody_coefficient_values
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (scratch : Cells ctx (activeScratchShapes width)) (scratchDistinct : scratch.Distinct)
    (cross : CrossSeparated cells scratch) (zero : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) :
    let quotient := CShape.wordResize (PureXGCD.executionCoefficientWidth width)
      (CShape.divRem width width (.product
        (store.read (GCD.cellRead (secondCell cells)))
        (store.read (GCD.cellRead (firstCell cells))))).first
    let final := activeBodyStore cells scratch zero store
    final.read (GCD.cellRead (firstLeftCell cells)) =
      Resource.WordBinaryOpcode.eval .sub (PureXGCD.executionCoefficientWidth width)
        (.product (store.read (GCD.cellRead (secondLeftCell cells)))
          (Resource.WordBinaryOpcode.eval .mulLow (PureXGCD.executionCoefficientWidth width)
            (.product quotient (store.read (GCD.cellRead (firstLeftCell cells)))))) ∧
    final.read (GCD.cellRead (secondLeftCell cells)) =
      store.read (GCD.cellRead (firstLeftCell cells)) ∧
    final.read (GCD.cellRead (firstRightCell cells)) =
      Resource.WordBinaryOpcode.eval .sub (PureXGCD.executionCoefficientWidth width)
        (.product (store.read (GCD.cellRead (secondRightCell cells)))
          (Resource.WordBinaryOpcode.eval .mulLow (PureXGCD.executionCoefficientWidth width)
            (.product quotient (store.read (GCD.cellRead (firstRightCell cells)))))) ∧
    final.read (GCD.cellRead (secondRightCell cells)) =
      store.read (GCD.cellRead (firstRightCell cells)) := by
  let divided := store.applyOp
    (GCD.divisionOp (firstCell cells) (secondCell cells) (activeDivisionCell scratch))
  let widened := divided.applyOp (activeResizeQuotientOp scratch)
  let left := coefficientUpdateStore (coefficientRead (activeQuotientCell scratch))
    (firstLeftCell cells) (secondLeftCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch) widened
  let right := coefficientUpdateStore (coefficientRead (activeQuotientCell scratch))
    (firstRightCell cells) (secondRightCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch) left
  have widenedState {shape : CShape} (cell : CWriteRef ctx shape) (index : Fin 7)
      (key : cell.key = stateKey cells index) :
      widened.read (GCD.cellRead cell) = store.read (GCD.cellRead cell) := by
    change (divided.applyOp (activeResizeQuotientOp scratch)).read _ = _
    rw [GCD.op_preserves_cell (activeResizeQuotientOp scratch) cell
      (by rw [key]; exact (cross_ne cells scratch cross index 1).symm)]
    exact GCD.op_preserves_cell _ cell
      (by rw [key]; exact (cross_ne cells scratch cross index 0).symm) store
  have widenedQuotient : widened.read (coefficientRead (activeQuotientCell scratch)) =
      CShape.wordResize (PureXGCD.executionCoefficientWidth width)
        (CShape.divRem width width (.product
          (store.read (GCD.cellRead (secondCell cells)))
          (store.read (GCD.cellRead (firstCell cells))))).first := by
    have actual := Store.read_applyOp_output divided (activeResizeQuotientOp scratch)
    change widened.read (coefficientRead (activeQuotientCell scratch)) =
      CShape.wordResize (PureXGCD.executionCoefficientWidth width)
        (divided.read (GCD.cellRead (activeDivisionCell scratch))).first at actual
    rw [GCD.division_read] at actual
    exact actual
  have leftValues := xgcdCoefficientUpdate_store_values
    (coefficientRead (activeQuotientCell scratch))
    (firstLeftCell cells) (secondLeftCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch)
    (state_ne cells distinct 2 4 (by decide))
    (cross_ne cells scratch cross 2 2).symm (cross_ne cells scratch cross 4 2).symm
    (cross_ne cells scratch cross 2 3).symm (cross_ne cells scratch cross 4 3) widened
  have leftPreserves {shape : CShape} (cell : CWriteRef ctx shape) (index : Fin 7)
      (key : cell.key = stateKey cells index) (firstFree : (2 : Fin 7) ≠ index)
      (secondFree : (4 : Fin 7) ≠ index) :
      left.read (GCD.cellRead cell) = widened.read (GCD.cellRead cell) := by
    apply coefficient_preserves_cell
    · rw [key]; exact state_ne cells distinct 2 index firstFree
    · rw [key]; exact state_ne cells distinct 4 index secondFree
    · rw [key]; exact (cross_ne cells scratch cross index 2).symm
    · rw [key]; exact (cross_ne cells scratch cross index 3).symm
  have leftQuotient : left.read (coefficientRead (activeQuotientCell scratch)) =
      widened.read (coefficientRead (activeQuotientCell scratch)) := by
    apply coefficient_preserves_cell
    · exact cross_ne cells scratch cross 2 1
    · exact cross_ne cells scratch cross 4 1
    · exact scratch_ne scratch scratchDistinct 2 1 (by decide)
    · exact scratch_ne scratch scratchDistinct 3 1 (by decide)
  have rightValues := xgcdCoefficientUpdate_store_values
    (coefficientRead (activeQuotientCell scratch))
    (firstRightCell cells) (secondRightCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch)
    (state_ne cells distinct 3 5 (by decide))
    (cross_ne cells scratch cross 3 2).symm (cross_ne cells scratch cross 5 2).symm
    (cross_ne cells scratch cross 3 3).symm (cross_ne cells scratch cross 5 3) left
  have rightPreserves {shape : CShape} (cell : CWriteRef ctx shape) (index : Fin 7)
      (key : cell.key = stateKey cells index) (firstFree : (3 : Fin 7) ≠ index)
      (secondFree : (5 : Fin 7) ≠ index) :
      right.read (GCD.cellRead cell) = left.read (GCD.cellRead cell) := by
    apply coefficient_preserves_cell
    · rw [key]; exact state_ne cells distinct 3 index firstFree
    · rw [key]; exact state_ne cells distinct 5 index secondFree
    · rw [key]; exact (cross_ne cells scratch cross index 2).symm
    · rw [key]; exact (cross_ne cells scratch cross index 3).symm
  have tailPreserves {shape : CShape} (cell : CWriteRef ctx shape) (index : Fin 7)
      (key : cell.key = stateKey cells index)
      (firstFree : (0 : Fin 7) ≠ index) (secondFree : (1 : Fin 7) ≠ index)
      (activeFree : (6 : Fin 7) ≠ index) :
      (activeBodyStore cells scratch zero store).read (GCD.cellRead cell) =
        right.read (GCD.cellRead cell) := by
    change ((((right.applyOp (GCD.rotateSecondOp (firstCell cells) (secondCell cells))).applyOp
      (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch))).applyOp
        (GCD.testActiveOp (firstCell cells) zero (activeCell cells))).applyOp
          (GCD.negateActiveOp (activeCell cells))).read _ = _
    rw [GCD.op_preserves_cell (GCD.negateActiveOp (activeCell cells)) cell
        (by rw [key]; exact state_ne cells distinct 6 index activeFree),
      GCD.op_preserves_cell (GCD.testActiveOp (firstCell cells) zero (activeCell cells)) cell
        (by rw [key]; exact state_ne cells distinct 6 index activeFree),
      GCD.op_preserves_cell
        (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch)) cell
        (by rw [key]; exact state_ne cells distinct 0 index firstFree),
      GCD.op_preserves_cell (GCD.rotateSecondOp (firstCell cells) (secondCell cells)) cell
        (by rw [key]; exact state_ne cells distinct 1 index secondFree)]
  have leftFirst : left.read (GCD.cellRead (firstLeftCell cells)) =
      Resource.WordBinaryOpcode.eval .sub (PureXGCD.executionCoefficientWidth width)
        (.product (widened.read (GCD.cellRead (secondLeftCell cells)))
          (Resource.WordBinaryOpcode.eval .mulLow (PureXGCD.executionCoefficientWidth width)
            (.product (widened.read (coefficientRead (activeQuotientCell scratch)))
              (widened.read (GCD.cellRead (firstLeftCell cells)))))) := leftValues.1
  have leftSecond : left.read (GCD.cellRead (secondLeftCell cells)) =
      widened.read (GCD.cellRead (firstLeftCell cells)) := leftValues.2
  have rightFirst : right.read (GCD.cellRead (firstRightCell cells)) =
      Resource.WordBinaryOpcode.eval .sub (PureXGCD.executionCoefficientWidth width)
        (.product (left.read (GCD.cellRead (secondRightCell cells)))
          (Resource.WordBinaryOpcode.eval .mulLow (PureXGCD.executionCoefficientWidth width)
            (.product (left.read (coefficientRead (activeQuotientCell scratch)))
              (left.read (GCD.cellRead (firstRightCell cells)))))) := rightValues.1
  have rightSecond : right.read (GCD.cellRead (secondRightCell cells)) =
      left.read (GCD.cellRead (firstRightCell cells)) := rightValues.2
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tailPreserves (firstLeftCell cells) 2 rfl (by decide) (by decide) (by decide),
      rightPreserves (firstLeftCell cells) 2 rfl (by decide) (by decide), leftFirst,
      widenedQuotient, widenedState (firstLeftCell cells) 2 rfl,
      widenedState (secondLeftCell cells) 4 rfl]
  · rw [tailPreserves (secondLeftCell cells) 4 rfl (by decide) (by decide) (by decide),
      rightPreserves (secondLeftCell cells) 4 rfl (by decide) (by decide), leftSecond,
      widenedState (firstLeftCell cells) 2 rfl]
  · rw [tailPreserves (firstRightCell cells) 3 rfl (by decide) (by decide) (by decide),
      rightFirst, leftQuotient, widenedQuotient,
      leftPreserves (firstRightCell cells) 3 rfl (by decide) (by decide),
      leftPreserves (secondRightCell cells) 5 rfl (by decide) (by decide),
      widenedState (firstRightCell cells) 3 rfl, widenedState (secondRightCell cells) 5 rfl]
  · rw [tailPreserves (secondRightCell cells) 5 rfl (by decide) (by decide) (by decide),
      rightSecond, leftPreserves (firstRightCell cells) 3 rfl (by decide) (by decide),
      widenedState (firstRightCell cells) 3 rfl]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
