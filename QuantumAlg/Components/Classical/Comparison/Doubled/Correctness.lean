/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Comparison.Doubled

/-!
# Actual doubled-word comparison correctness

The final bit is obtained from the actual shifted word and actual comparison.
Original unsigned capacity conditions turn the modular result into the exact
integer inequality without a caller-supplied execution or result certificate.
-/

namespace QuantumAlg.ClassicalRoutines.Comparison.Doubled

open NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma double_read (refs : Refs ctx width) (store : Store ctx) :
    (store.applyOp (doubleOp refs)).read (.storage refs.doubled.toCStorageRef) =
      Resource.WordUnaryOpcode.eval .shiftLeft width (store.read refs.right) := by
  change (store.applyOp (doubleOp refs)).read
    (.storage (doubleOp refs).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  rfl

private lemma compare_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (compareOp refs)).read (.storage refs.passes.toCStorageRef)).toBool =
      decide ((store.read (.storage refs.doubled.toCStorageRef)).toNat <
        (store.read refs.left).toNat) := by
  simp only [Store.applyOp, compareOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval]
  rfl

private lemma complement_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (complementOp refs)).read (.storage refs.passes.toCStorageRef)).toBool =
      !(store.read (.storage refs.passes.toCStorageRef)).toBool := by
  simp only [Store.applyOp, complementOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval]
  cases store.read (.storage refs.passes.toCStorageRef)
  rfl

/-- The actual final scratch word is the actual original right input shifted left once. -/
lemma compareInto_doubled (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (comparedStore refs store).read (.storage refs.doubled.toCStorageRef) =
      Resource.WordUnaryOpcode.eval .shiftLeft width (store.read refs.right) := by
  have avoids : refs.passes.key ∉
      (CInputRef.storage refs.doubled.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.doubledAvoidsPass
  unfold comparedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (complementOp refs) _ avoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (compareOp refs) _ avoids, double_read]

/-- The actual final Boolean is the exact comparison against the modular shifted right word. -/
lemma compareInto_raw (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    ((comparedStore refs store).read (.storage refs.passes.toCStorageRef)).toBool =
      decide ((store.read refs.left).toNat ≤
        (Resource.WordUnaryOpcode.eval .shiftLeft width (store.read refs.right)).toNat) := by
  unfold comparedStore
  rw [complement_read, compare_read, double_read,
    Store.read_applyOp_of_not_mem_storageKeys store (doubleOp refs) refs.left
      separation.leftAvoidsDoubled]
  simp only [← decide_not, Nat.not_lt]

/-- Under the original capacity bounds, the final actual bit decides the integer inequality. -/
lemma compareInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (left right : Nat)
    (leftRep : RawSignedRepresents (store.read refs.left) (left : Int))
    (rightRep : RawSignedRepresents (store.read refs.right) (right : Int))
    (leftFits : left < CShape.wordModulus width)
    (doubledFits : 2 * right < CShape.wordModulus width) :
    ((comparedStore refs store).read (.storage refs.passes.toCStorageRef)).toBool =
      decide (left ≤ 2 * right) := by
  have leftValue := rawSignedRepresents_toNat_eq_of_lt _ leftRep leftFits
  have shiftedRep : RawSignedRepresents
      (Resource.WordUnaryOpcode.eval .shiftLeft width (store.read refs.right))
      ((2 * right : Nat) : Int) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      rawSignedWordRepresents_shiftLeft (store.read refs.right) (right : Int) rightRep
  have shiftedValue := rawSignedRepresents_toNat_eq_of_lt _ shiftedRep doubledFits
  rw [compareInto_raw refs separation store, leftValue, shiftedValue]

/-- Both original structural inputs retain their actual values after the comparison. -/
lemma compareInto_preserves_inputs (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (comparedStore refs store).read refs.left = store.read refs.left ∧
      (comparedStore refs store).read refs.right = store.read refs.right :=
  ⟨compareInto_callerFrame refs store refs.left
      separation.leftAvoidsDoubled separation.leftAvoidsPass,
    compareInto_callerFrame refs store refs.right
      separation.rightAvoidsDoubled separation.rightAvoidsPass⟩

end

end QuantumAlg.ClassicalRoutines.Comparison.Doubled
