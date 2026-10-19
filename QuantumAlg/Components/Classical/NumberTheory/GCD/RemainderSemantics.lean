/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Step
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Store arithmetic of the literal Euclidean update

The separation facts concern actual allocated cell identities. They are
discharged by the lexical layout, rather than imposed on the GCD input.
The equations allow every initial value of the active bit and division
scratch. Even the comparison cell may initially contain an arbitrary word:
its zero value is established later by the retained allocation.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma op_preserves_cell {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ other.key) (store : Store ctx) :
    (store.applyOp op).read (cellRead other) = store.read (cellRead other) :=
  Store.read_write_other store op.outputRef other.toCStorageRef _ different

private lemma division_read (first second : CWriteRef ctx (.unsignedWord width))
    (scratch : CWriteRef ctx (operandShape width)) (store : Store ctx) :
    (store.applyOp (divisionOp first second scratch)).read (cellRead scratch) =
      CShape.divRem width width (.product
        (store.read (cellRead second)) (store.read (cellRead first))) :=
  Store.read_applyOp_output store (divisionOp first second scratch)

private lemma rotate_read (first second : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (store.applyOp (rotateSecondOp first second)).read (cellRead second) =
      store.read (cellRead first) :=
  Store.read_applyOp_output store (rotateSecondOp first second)

private lemma remainder_read (first : CWriteRef ctx (.unsignedWord width))
    (scratch : CWriteRef ctx (operandShape width)) (store : Store ctx) :
    (store.applyOp (takeRemainderOp first scratch)).read (cellRead first) =
      (store.read (cellRead scratch)).second :=
  Store.read_applyOp_output store (takeRemainderOp first scratch)

private lemma test_read (first : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) :
    ((store.applyOp (testActiveOp first zero active)).read (cellRead active)).toBool =
      decide ((store.read (cellRead first)).toNat = (store.read zero).toNat) :=
  congrArg CShape.Value.toBool (Store.read_applyOp_output store (testActiveOp first zero active))

private lemma negate_read (active : CWriteRef ctx .bit) (store : Store ctx) :
    ((store.applyOp (negateActiveOp active)).read (cellRead active)).toBool =
      !(store.read (cellRead active)).toBool := by
  have actual := congrArg CShape.Value.toBool
    (Store.read_applyOp_output store (negateActiveOp active))
  change ((store.applyOp (negateActiveOp active)).read (cellRead active)).toBool =
    ((negateActiveOp active).eval (store.read (cellRead active))).toBool at actual
  cases value : store.read (cellRead active) with
  | bit bit =>
      rw [value] at actual
      exact actual

/-- Every structural read outside the four written cells is preserved exactly. -/
lemma gcdRemainder_read_other (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) {observed : CShape}
    (other : CInputRef ctx observed)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (scratchFree : scratch.key ∉ other.storageKeys)
    (store : Store ctx) :
    (remainderStore first second zero active scratch store).read other = store.read other := by
  unfold remainderStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (negateActiveOp active) other activeFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (testActiveOp first zero active) other activeFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (takeRemainderOp first scratch) other firstFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (rotateSecondOp first second) other secondFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (divisionOp first second scratch) other scratchFree]

/-- The actual cells contain the exact remainder, old divisor and refreshed comparison bit. -/
lemma gcdRemainder_store_values (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (firstSecond : first.key ≠ second.key) (scratchFirst : scratch.key ≠ first.key)
    (secondScratch : second.key ≠ scratch.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (scratchZero : scratch.key ∉ zero.storageKeys)
    (store : Store ctx) :
    let final := remainderStore first second zero active scratch store
    (final.read (cellRead first)).toNat =
        (store.read (cellRead second)).toNat % (store.read (cellRead first)).toNat ∧
      final.read (cellRead second) = store.read (cellRead first) ∧
      (final.read (cellRead active)).toBool =
        decide ((store.read (cellRead second)).toNat %
          (store.read (cellRead first)).toNat ≠ (store.read zero).toNat) ∧
      final.read zero = store.read zero := by
  let divided := store.applyOp (divisionOp first second scratch)
  let rotated := divided.applyOp (rotateSecondOp first second)
  let reduced := rotated.applyOp (takeRemainderOp first scratch)
  let tested := reduced.applyOp (testActiveOp first zero active)
  have dividedFirst : divided.read (cellRead first) = store.read (cellRead first) :=
    op_preserves_cell (divisionOp first second scratch) first scratchFirst store
  have rotatedScratch : rotated.read (cellRead scratch) = divided.read (cellRead scratch) :=
    op_preserves_cell (rotateSecondOp first second) scratch secondScratch divided
  have reducedFirst : (reduced.read (cellRead first)).toNat =
      (store.read (cellRead second)).toNat % (store.read (cellRead first)).toNat := by
    rw [remainder_read first scratch rotated, rotatedScratch, division_read]
    exact gcdOperands_divRem_remainder _ _
  have reducedSecond : reduced.read (cellRead second) = store.read (cellRead first) := by
    rw [op_preserves_cell (takeRemainderOp first scratch) second firstSecond rotated,
      rotate_read, dividedFirst]
  have reducedZero : reduced.read zero = store.read zero := by
    dsimp only [reduced, rotated, divided]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (takeRemainderOp first scratch) zero firstZero,
      Store.read_applyOp_of_not_mem_storageKeys _ (rotateSecondOp first second) zero secondZero,
      Store.read_applyOp_of_not_mem_storageKeys _ (divisionOp first second scratch)
        zero scratchZero]
  dsimp only
  refine ⟨?_, ?_, ?_, gcdRemainder_read_other first second zero active scratch zero
    firstZero secondZero activeZero scratchZero store⟩
  · change ((tested.applyOp (negateActiveOp active)).read (cellRead first)).toNat = _
    rw [op_preserves_cell (negateActiveOp active) first activeFirst tested,
      op_preserves_cell (testActiveOp first zero active) first activeFirst reduced]
    exact reducedFirst
  · change (tested.applyOp (negateActiveOp active)).read (cellRead second) = _
    rw [op_preserves_cell (negateActiveOp active) second activeSecond tested,
      op_preserves_cell (testActiveOp first zero active) second activeSecond reduced]
    exact reducedSecond
  · change ((tested.applyOp (negateActiveOp active)).read (cellRead active)).toBool = _
    rw [negate_read, test_read first zero active reduced, reducedFirst, reducedZero]
    simp

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
