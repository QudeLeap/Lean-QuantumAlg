/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Separation

/-!
# Both actual stored validity bits refer to the original candidate words

The first real remainder write is the only checker write to an original
cell. Internal separation of that reused word preserves the source operands
for the second complete check. Its fresh destinations preserve the first
validity result. Consequently both decisions coexist before selection and
refer to the same original modulus, constant and candidate values.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual reused remainder word differs from the four still-live source reads. -/
structure OperandsSeparated (inputs : Operands ctx width) : Prop where
  remainderModulus : inputs.remainder.key ∉ inputs.modulus.storageKeys
  remainderOne : inputs.remainder.key ∉ inputs.one.storageKeys
  remainderFirst : inputs.remainder.key ∉ inputs.first.storageKeys
  remainderSecond : inputs.remainder.key ∉ inputs.second.storageKeys

/-- The first actual check preserves every lifted old read outside the reused remainder cell. -/
theorem nativeQuadratic_first_check_read_original (inputs : Operands ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (remainderFree : inputs.remainder.key ∉ other.storageKeys)
    (store : Store (context ctx width)) :
    (Check.storeStep (pairRefs inputs).first store).read (underRead other width) =
      store.read (underRead other width) := by
  have reused : (underWrite inputs.remainder width).key ∉
      (underRead other width).storageKeys := by
    rw [nativeQuadratic_checkLayout_underWrite_key, nativeQuadratic_checkLayout_underRead_keys]
    exact remainderFree
  exact Check.nativeQuadratic_check_read_other (pairRefs inputs).first (underRead other width)
    (nativeQuadratic_checkLayout_new_free other width (firstValid ctx width).key
      (by simp [internalKeys]))
    (nativeQuadratic_checkLayout_new_free other width (upper ctx width).key
      (by simp [internalKeys])) reused
    (nativeQuadratic_checkLayout_new_free other width (divides ctx width).key
      (by simp [internalKeys])) store

/-- The second actual check preserves the same original reads while writing its own result bit. -/
theorem nativeQuadratic_second_check_read_original (inputs : Operands ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (remainderFree : inputs.remainder.key ∉ other.storageKeys)
    (store : Store (context ctx width)) :
    (Check.storeStep (pairRefs inputs).second store).read (underRead other width) =
      store.read (underRead other width) := by
  have reused : (underWrite inputs.remainder width).key ∉
      (underRead other width).storageKeys := by
    rw [nativeQuadratic_checkLayout_underWrite_key, nativeQuadratic_checkLayout_underRead_keys]
    exact remainderFree
  exact Check.nativeQuadratic_check_read_other (pairRefs inputs).second (underRead other width)
    (nativeQuadratic_checkLayout_new_free other width (secondValid ctx width).key
      (by simp [internalKeys]))
    (nativeQuadratic_checkLayout_new_free other width (upper ctx width).key
      (by simp [internalKeys])) reused
    (nativeQuadratic_checkLayout_new_free other width (divides ctx width).key
      (by simp [internalKeys])) store

/-- Both checks preserve the full value of every original read outside the remainder destination. -/
theorem nativeQuadratic_checks_read_original (inputs : Operands ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (remainderFree : inputs.remainder.key ∉ other.storageKeys)
    (store : Store (context ctx width)) :
    (Pair.checkedStore (pairRefs inputs) store).read (underRead other width) =
      store.read (underRead other width) :=
  (nativeQuadratic_second_check_read_original inputs other remainderFree
    (Check.storeStep (pairRefs inputs).first store)).trans
    (nativeQuadratic_first_check_read_original inputs other remainderFree store)

private theorem divides_zero (ctx : RuntimeCtx kind) (width : Nat) :
    (divides ctx width).key ≠ (zero ctx width).key := by
  have unique := nativeQuadratic_checkLayout_nodup ctx width
  simp only [internalKeys, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at unique
  exact unique.2.2.1.2

/-- The first complete check retains the real zero operand consumed again by the second check. -/
theorem nativeQuadratic_first_check_read_zero (inputs : Operands ctx width)
    (store : Store (context ctx width)) :
    (Check.storeStep (pairRefs inputs).first store).read
        (.storage (zero ctx width).toCStorageRef) =
      store.read (.storage (zero ctx width).toCStorageRef) := by
  have separate := nativeQuadratic_first_check_separated inputs
  exact Check.nativeQuadratic_check_read_other (pairRefs inputs).first
    (.storage (zero ctx width).toCStorageRef)
    separate.validZero separate.upperZero separate.remainderZero
    (fun present => divides_zero ctx width (List.mem_singleton.mp present)) store

/-- The second complete check preserves the first actual validity bit. -/
theorem nativeQuadratic_second_check_read_first (inputs : Operands ctx width)
    (store : Store (context ctx width)) :
    (Check.storeStep (pairRefs inputs).second store).read
        (.storage (firstValid ctx width).toCStorageRef) =
      store.read (.storage (firstValid ctx width).toCStorageRef) := by
  have separate := nativeQuadratic_first_check_separated inputs
  exact Check.nativeQuadratic_check_read_other (pairRefs inputs).second
    (.storage (firstValid ctx width).toCStorageRef)
    (fun present => (nativeQuadratic_checkLayout_valid_distinct ctx width).symm
      (List.mem_singleton.mp present))
    (fun present => separate.upperValid (List.mem_singleton.mp present))
    (fun present => separate.remainderValid (List.mem_singleton.mp present))
    (fun present => separate.dividesValid (List.mem_singleton.mp present)) store

/-- Both stored validity bits equal their original strict-range and natural-remainder tests. -/
theorem nativeQuadratic_checks_values (inputs : Operands ctx width)
    (separate : OperandsSeparated inputs) (store : Store (context ctx width))
    (oneValue : (store.read (underRead inputs.one width)).toNat = 1)
    (zeroValue : (store.read (.storage (zero ctx width).toCStorageRef)).toNat = 0) :
    let final := Pair.checkedStore (pairRefs inputs) store
    (final.read (.storage (firstValid ctx width).toCStorageRef)).toBool =
        decide (1 < (store.read (underRead inputs.first width)).toNat ∧
          (store.read (underRead inputs.first width)).toNat <
            (store.read (underRead inputs.modulus width)).toNat ∧
          (store.read (underRead inputs.modulus width)).toNat %
            (store.read (underRead inputs.first width)).toNat = 0) ∧
      (final.read (.storage (secondValid ctx width).toCStorageRef)).toBool =
        decide (1 < (store.read (underRead inputs.second width)).toNat ∧
          (store.read (underRead inputs.second width)).toNat <
            (store.read (underRead inputs.modulus width)).toNat ∧
          (store.read (underRead inputs.modulus width)).toNat %
            (store.read (underRead inputs.second width)).toNat = 0) := by
  let firstStore := Check.storeStep (pairRefs inputs).first store
  have firstResult := Check.nativeQuadratic_check_read_constants (pairRefs inputs).first
    (nativeQuadratic_first_check_separated inputs) store oneValue zeroValue
  have firstStill := congrArg CShape.Value.toBool
    (nativeQuadratic_second_check_read_first inputs firstStore)
  have oneStill := congrArg CShape.Value.toNat
    (nativeQuadratic_first_check_read_original inputs inputs.one separate.remainderOne store)
  have zeroStill := congrArg CShape.Value.toNat (nativeQuadratic_first_check_read_zero inputs store)
  have modulusStill := congrArg CShape.Value.toNat
    (nativeQuadratic_first_check_read_original inputs inputs.modulus
      separate.remainderModulus store)
  have secondStill := congrArg CShape.Value.toNat
    (nativeQuadratic_first_check_read_original inputs inputs.second separate.remainderSecond store)
  have secondResult := Check.nativeQuadratic_check_read_constants (pairRefs inputs).second
    (nativeQuadratic_second_check_separated inputs) firstStore
    (oneStill.trans oneValue) (zeroStill.trans zeroValue)
  refine ⟨firstStill.trans firstResult, secondResult.trans ?_⟩
  exact congrArg₂ (fun modulus candidate : Nat =>
    decide (1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0))
    modulusStill secondStill

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
