/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Divisibility.Readout

/-!
# Stored candidate validity from all actual native checks

The shared range circuit and the actual divisibility circuit consume the same
preserved source words. The result is the original conjunction of strict range
and zero remainder, after the enclosing scope establishes its actual one and
zero cells. All non-source temporary bits may initially contain arbitrary values.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Check

open Execution
open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Internal separation of actual shared comparison and remainder cells. -/
structure Separated (refs : Refs ctx width) : Prop where
  /-- The first comparison preserves the modulus. -/
  validModulus : refs.divisor.valid.key ∉ refs.divisor.modulus.storageKeys
  /-- The first comparison preserves the candidate. -/
  validCandidate : refs.divisor.valid.key ∉ refs.divisor.candidate.storageKeys
  /-- The first comparison preserves the real zero cell. -/
  validZero : refs.divisor.valid.key ∉ refs.divisor.zero.storageKeys
  /-- The second comparison preserves the modulus. -/
  upperModulus : refs.upper.key ∉ refs.divisor.modulus.storageKeys
  /-- The second comparison preserves the candidate. -/
  upperCandidate : refs.upper.key ∉ refs.divisor.candidate.storageKeys
  /-- The second comparison preserves the zero cell. -/
  upperZero : refs.upper.key ∉ refs.divisor.zero.storageKeys
  /-- Both comparison bits coexist at their actual distinct positions. -/
  upperValid : refs.upper.key ≠ refs.divisor.valid.key
  /-- Remainder does not overwrite the zero word used by equality. -/
  remainderZero : refs.divisor.remainder.key ∉ refs.divisor.zero.storageKeys
  /-- Computing the remainder preserves the actual range result. -/
  remainderValid : refs.divisor.remainder.key ≠ refs.divisor.valid.key
  /-- Equality preserves that same range result for conjunction. -/
  dividesValid : refs.divisor.divides.key ≠ refs.divisor.valid.key

/-- All six actual instructions return the range and remainder test on the original words. -/
theorem nativeQuadratic_check_read (refs : Refs ctx width) (separated : Separated refs)
    (store : Store ctx) :
    ((storeStep refs store).read (.storage refs.divisor.valid.toCStorageRef)).toBool =
      ((decide ((store.read refs.one).toNat < (store.read refs.divisor.candidate).toNat) &&
        decide ((store.read refs.divisor.candidate).toNat <
          (store.read refs.divisor.modulus).toNat)) &&
          decide ((store.read refs.divisor.modulus).toNat %
            (store.read refs.divisor.candidate).toNat = (store.read refs.divisor.zero).toNat)) := by
  let ranged := FactorRange.storeStep (rangeRefs refs) store
  have lowerFree : refs.divisor.valid.key ∉
      (CInputRef.product refs.divisor.candidate refs.divisor.modulus).storageKeys := by
    simp only [CInputRef.storageKeys, List.mem_append, not_or]
    exact ⟨separated.validCandidate, separated.validModulus⟩
  have rangeValue : (ranged.read (.storage refs.divisor.valid.toCStorageRef)).toBool =
      (decide ((store.read refs.one).toNat < (store.read refs.divisor.candidate).toNat) &&
        decide ((store.read refs.divisor.candidate).toNat <
          (store.read refs.divisor.modulus).toNat)) :=
    FactorRange.result (rangeRefs refs) store lowerFree separated.upperValid
  have modulusValue := FactorRange.read_other (rangeRefs refs) refs.divisor.modulus
    separated.validModulus separated.upperModulus store
  have candidateValue := FactorRange.read_other (rangeRefs refs) refs.divisor.candidate
    separated.validCandidate separated.upperCandidate store
  have zeroValue := FactorRange.read_other (rangeRefs refs) refs.divisor.zero
    separated.validZero separated.upperZero store
  have divided := Divisibility.nativeQuadratic_divisibility_read refs.divisor ranged
    separated.remainderZero separated.remainderValid separated.dividesValid
  refine divided.trans ?_
  rw [rangeValue, modulusValue, candidateValue, zeroValue]

/-- Real one and zero cell values specialize the stored result to the exact source validity test. -/
theorem nativeQuadratic_check_read_constants (refs : Refs ctx width)
    (separated : Separated refs) (store : Store ctx)
    (oneValue : (store.read refs.one).toNat = 1)
    (zeroValue : (store.read refs.divisor.zero).toNat = 0) :
    ((storeStep refs store).read (.storage refs.divisor.valid.toCStorageRef)).toBool =
      decide (1 < (store.read refs.divisor.candidate).toNat ∧
        (store.read refs.divisor.candidate).toNat < (store.read refs.divisor.modulus).toNat ∧
        (store.read refs.divisor.modulus).toNat %
          (store.read refs.divisor.candidate).toNat = 0) := by
  rw [nativeQuadratic_check_read refs separated store, oneValue, zeroValue]
  simp only [Bool.decide_and, Bool.and_assoc]

/-- Every original structural read outside the actual four written cells keeps its full value. -/
theorem nativeQuadratic_check_read_other (refs : Refs ctx width) {shape : CShape}
    (other : CInputRef ctx shape) (validFree : refs.divisor.valid.key ∉ other.storageKeys)
    (upperFree : refs.upper.key ∉ other.storageKeys)
    (remainderFree : refs.divisor.remainder.key ∉ other.storageKeys)
    (dividesFree : refs.divisor.divides.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep refs store).read other = store.read other :=
  (Divisibility.nativeQuadratic_divisibility_read_other refs.divisor other
    remainderFree dividesFree validFree (FactorRange.storeStep (rangeRefs refs) store)).trans
    (FactorRange.read_other (rangeRefs refs) other validFree upperFree store)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Check
