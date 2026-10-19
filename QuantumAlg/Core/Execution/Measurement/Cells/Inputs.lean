/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Store

/-!
# Existing classical operands under actual measurement-cell allocations

Structural references keep reading their original cells underneath every
new retained result cell. Lifting a reference adds no circuit instruction,
copy, reconstruction, or physical storage.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

open QuantumAlg.Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}

/-- Keep an original structural operand underneath all actual result cells. -/
def liftInput (dimension : ℕ+) (input : CInputRef ctx shape) :
    (count : Nat) → CInputRef (context ctx dimension count) shape
  | 0 => input
  | count + 1 =>
      (liftInput dimension input count).underRetained
        (context ctx dimension count).canonicalFreshKey (.finite dimension)
        (context ctx dimension count).canonicalFreshKey_fresh

/-- A product of actual earlier inputs keeps its structural components under allocation. -/
lemma liftInput_product {left right : CShape} (dimension : ℕ+)
    (first : CInputRef ctx left) (second : CInputRef ctx right) (count : Nat) :
    liftInput dimension (.product first second) count =
      .product (liftInput dimension first count) (liftInput dimension second count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [liftInput, induction]
      rfl

/-- The actual allocations preserve the value read through the lifted operand. -/
lemma read_pushStore_liftInput (dimension : ℕ+) (count : Nat)
    (store : Store ctx) (input : CInputRef ctx shape) :
    (pushStore dimension count store).read (liftInput dimension input count) =
      store.read input := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [pushStore, liftInput, Store.read_pushRetained_underRetained]
      exact induction

/-- Lifting a writable storage read yields the same old-cell operand. -/
lemma liftInput_storage (dimension : ℕ+) (ref : CWriteRef ctx shape) (count : Nat) :
    liftInput dimension (.storage ref.toCStorageRef) count =
      .storage (liftWrite dimension ref count).toCStorageRef := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [liftInput, induction, liftWrite]
      rfl

end

end QuantumAlg.Execution.MeasurementCells
