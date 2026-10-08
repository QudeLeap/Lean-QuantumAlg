/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision.Scope
import all QuantumAlg.Util.Classical.GF2

/-!
# The actual free-mask decision identifies the original sole free column

The represented mask and zero value are intermediate facts established by
actual allocation and reduction. The incoming success bit remains arbitrary.
The real fixed-width subtraction and conjunction implement the original pure
single-bit criterion, including the zero-width and zero-mask cases.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

omit [BitWord.Selected model] in
private theorem clear_lowest (mask : Fin (2 ^ width)) (nonzero : mask.val ≠ 0) :
    (CShape.wordBitAnd width (.unsignedWord mask)
      (CShape.wordSub width (.unsignedWord mask) (CShape.wordOfNat width 1))).toNat =
      mask.val &&& (mask.val - 1) := by
  have range : mask.val < CShape.wordModulus width := mask.isLt
  have positive : 0 < mask.val := Nat.pos_of_ne_zero nonzero
  have oneFits : 1 < CShape.wordModulus width := by omega
  have differenceRange : mask.val - 1 < CShape.wordModulus width :=
    (Nat.sub_le mask.val 1).trans_lt range
  have split : mask.val + CShape.wordModulus width -
      (CShape.wordOfNat width 1).toNat = (mask.val - 1) + CShape.wordModulus width := by
    rw [CShape.wordOfNat_val, Nat.mod_eq_of_lt oneFits]
    omega
  have difference : (CShape.wordSub width (.unsignedWord mask)
      (CShape.wordOfNat width 1)).toNat = mask.val - 1 := by
    change (mask.val + CShape.wordModulus width -
      (CShape.wordOfNat width 1).toNat) % CShape.wordModulus width = mask.val - 1
    rw [split, Nat.add_mod_right, Nat.mod_eq_of_lt differenceRange]
  have maskedRange : mask.val &&& (mask.val - 1) < CShape.wordModulus width :=
    Nat.lt_of_le_of_lt Nat.and_le_left range
  change (mask.val &&& (CShape.wordSub width (.unsignedWord mask)
    (CShape.wordOfNat width 1)).toNat) % CShape.wordModulus width = _
  rw [difference, Nat.mod_eq_of_lt maskedRange]

omit [BitWord.Selected model] in
private theorem represented_test (result : ClassicalAlgorithms.GF2.Result rowCount width) :
    ((CShape.wordBitAnd width (.unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result))
      (CShape.wordSub width (.unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result))
        (CShape.wordOfNat width 1))).toNat = 0 ∧
      (ClassicalAlgorithms.GF2.freeColumnMask result).val ≠ 0) ↔
      ∃ free, ClassicalAlgorithms.GF2.soleFreeColumn? result = some free := by
  rw [← ClassicalAlgorithms.GF2.freeColumnMask_singleBit_iff_exists_soleFreeColumn]
  constructor
  · rintro ⟨cleared, nonzero⟩
    refine ⟨?_, (clear_lowest _ nonzero).symm.trans cleared⟩
    intro zero
    exact nonzero (congrArg Fin.val zero)
  · rintro ⟨nonzero, cleared⟩
    have valueNonzero : (ClassicalAlgorithms.GF2.freeColumnMask result).val ≠ 0 := by
      intro zero
      exact nonzero (Fin.ext zero)
    exact ⟨(clear_lowest _ valueNonzero).trans cleared, valueNonzero⟩

omit [BitWord.Selected model] in
private theorem bool_test (before : Bool) (left right zeroValue : Nat) :
    (before && decide (left = zeroValue) && !decide (right = zeroValue)) = true ↔
      before = true ∧ left = zeroValue ∧ right ≠ zeroValue := by
  by_cases leftZero : left = zeroValue <;> by_cases rightZero : right = zeroValue <;>
    cases before <;> simp [leftZero, rightZero]

/-- The actual scoped test succeeds precisely on an incoming success and one pure free column. -/
theorem gf2UniqueFree_success_iff (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx)
    (result : ClassicalAlgorithms.GF2.Result rowCount width)
    (freeValue : store.read (.storage free.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result))
    (zeroValue : store.read (.storage zero.toCStorageRef) = CShape.wordOfNat width 0) :
    ((selectUniqueFreeStep free zero success store).1.read
      (.storage success.toCStorageRef)).toBool = true ↔
      (store.read (.storage success.toCStorageRef)).toBool = true ∧
        ∃ column, ClassicalAlgorithms.GF2.soleFreeColumn? result = some column := by
  rw [gf2UniqueFree_success, bool_test, freeValue, zeroValue]
  have zeroNat : (CShape.wordOfNat width 0).toNat = 0 := by
    simp only [CShape.wordOfNat, CShape.Value.toNat, Nat.zero_mod]
  rw [zeroNat]
  exact and_congr_right (fun _ => represented_test result)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
