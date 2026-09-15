/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Divisibility
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact reads of the actual remainder and validity conjunction

Natural remainder fits the same word even at divisor zero. The comparison
uses the actual stored zero-word value, and the conjunction uses the actual
earlier range result. The enclosing real layout supplies separation and
initializes its zero cell; this leaf never substitutes assumed clean inputs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Divisibility

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual native remainder is exact for every divisor word, including zero and width zero. -/
theorem nativeQuadratic_remainder_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (remainderOp refs)).read (.storage refs.remainder.toCStorageRef)).toNat =
      (store.read refs.modulus).toNat % (store.read refs.candidate).toNat := by
  change ((store.applyOp (remainderOp refs)).read
    (.storage (remainderOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact Nat.mod_eq_of_lt
    ((Nat.mod_le _ _).trans_lt (store.read refs.modulus).toNat_lt)

/-- The actual final bit conjoins the old range result and the computed remainder comparison. -/
theorem nativeQuadratic_divisibility_read (refs : Refs ctx width) (store : Store ctx)
    (zeroFree : refs.remainder.key ∉ refs.zero.storageKeys)
    (remainderValid : refs.remainder.key ≠ refs.valid.key)
    (dividesValid : refs.divides.key ≠ refs.valid.key) :
    ((storeStep refs store).read (.storage refs.valid.toCStorageRef)).toBool =
      ((store.read (.storage refs.valid.toCStorageRef)).toBool &&
        decide ((store.read refs.modulus).toNat % (store.read refs.candidate).toNat =
          (store.read refs.zero).toNat)) := by
  let divided := store.applyOp (remainderOp refs)
  let compared := divided.applyOp (equalityOp refs)
  have remainderValue := nativeQuadratic_remainder_read refs store
  have zeroValue : divided.read refs.zero = store.read refs.zero :=
    Store.read_applyOp_of_not_mem_storageKeys store (remainderOp refs) refs.zero zeroFree
  have decision : (compared.read (.storage refs.divides.toCStorageRef)).toBool =
      decide ((store.read refs.modulus).toNat % (store.read refs.candidate).toNat =
        (store.read refs.zero).toNat) := by
    have actual := congrArg CShape.Value.toBool
      (Store.read_applyOp_output divided (equalityOp refs))
    change (compared.read (.storage refs.divides.toCStorageRef)).toBool =
      decide ((divided.read (.storage refs.remainder.toCStorageRef)).toNat =
        (divided.read refs.zero).toNat) at actual
    exact actual.trans (congrArg₂ (fun first second : Nat => decide (first = second))
      remainderValue (congrArg CShape.Value.toNat zeroValue))
  have validValue : compared.read (.storage refs.valid.toCStorageRef) =
      store.read (.storage refs.valid.toCStorageRef) :=
    (Store.read_write_other divided (equalityOp refs).outputRef refs.valid.toCStorageRef _
      dividesValid).trans
      (Store.read_write_other store (remainderOp refs).outputRef refs.valid.toCStorageRef _
        remainderValid)
  refine (congrArg CShape.Value.toBool
    (Store.read_applyOp_output compared (combineOp refs))).trans ?_
  change (Resource.BitOpcode.eval .and
    (.product (compared.read (.storage refs.valid.toCStorageRef))
      (compared.read (.storage refs.divides.toCStorageRef)))).toBool = _
  have combined (left right : CShape.Value .bit) :
      (Resource.BitOpcode.eval .and (.product left right)).toBool =
        (left.toBool && right.toBool) := by
    cases left
    cases right
    rfl
  rw [combined, validValue, decision]

/-- Every original structural read outside the three actual destinations keeps its full value. -/
theorem nativeQuadratic_divisibility_read_other (refs : Refs ctx width) {shape : CShape}
    (other : CInputRef ctx shape) (remainderFree : refs.remainder.key ∉ other.storageKeys)
    (dividesFree : refs.divides.key ∉ other.storageKeys)
    (validFree : refs.valid.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep refs store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys
    ((store.applyOp (remainderOp refs)).applyOp (equalityOp refs))
    (combineOp refs) other validFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys (store.applyOp (remainderOp refs))
      (equalityOp refs) other dividesFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (remainderOp refs) other remainderFree))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Divisibility
