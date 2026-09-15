/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Preparation

/-!
# Actual signed rounding correction

The real addition constructs twice the magnitude plus the denominator.
Only the stored negative flag selects the one-unit correction. The same
execution doubles the denominator and preserves the sign for the quotient's
final restoration. Numeric bounds justify each native word operation.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem add_read (refs : BodyRefs ctx width) (store : Store ctx)
    (fits : (store.read (writeInput refs.wideNumerator)).toNat +
      (store.read (writeInput refs.wideDenominator)).toNat < CShape.wordModulus (width + 1)) :
    ((store.applyOp (addDenominatorOp refs)).read (writeInput refs.wideNumerator)).toNat =
      (store.read (writeInput refs.wideNumerator)).toNat +
        (store.read (writeInput refs.wideDenominator)).toNat := by
  change ((store.applyOp (addDenominatorOp refs)).read
    (.storage (addDenominatorOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact Nat.mod_eq_of_lt fits

private theorem decrement_read (refs : BodyRefs ctx width) (store : Store ctx)
    (positive : 0 < (store.read (writeInput refs.wideNumerator)).toNat) :
    ((store.applyOp (correctNumeratorOp refs)).read (writeInput refs.wideNumerator)).toNat =
      (store.read (writeInput refs.wideNumerator)).toNat - 1 := by
  let value := (store.read (writeInput refs.wideNumerator)).toNat
  let modulus := CShape.wordModulus (width + 1)
  have bounded : value < modulus := (store.read (writeInput refs.wideNumerator)).toNat_lt
  have oneFits : 1 < modulus := by omega
  change ((store.applyOp (correctNumeratorOp refs)).read
    (.storage (correctNumeratorOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change (value + modulus - 1 % modulus) % modulus = value - 1
  rw [Nat.mod_eq_of_lt oneFits]
  have split : value + modulus - 1 = (value - 1) + modulus := by
    change 0 < value at positive
    omega
  rw [split, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ((Nat.sub_le value 1).trans_lt bounded)

private theorem correction_frame (refs : BodyRefs ctx width) (flag : CShape.Value .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : refs.wideNumerator.key ∉ other.storageKeys) :
    ((correctionStep refs flag store).1).read other = store.read other := by
  cases flag with
  | bit flag =>
      cases flag
      · rfl
      · exact Store.read_applyOp_of_not_mem_storageKeys store _ other separate

private theorem correction_value (refs : BodyRefs ctx width) (flag : CShape.Value .bit)
    (store : Store ctx) (positive : 0 < (store.read (writeInput refs.wideNumerator)).toNat) :
    (((correctionStep refs flag store).1).read (writeInput refs.wideNumerator)).toNat =
      if flag.toBool then (store.read (writeInput refs.wideNumerator)).toNat - 1
      else (store.read (writeInput refs.wideNumerator)).toNat := by
  cases flag with
  | bit flag =>
      cases flag
      · rfl
      · exact decrement_read refs store positive

/-- All actual rounding writes remain within the two wider operand cells. -/
theorem rounding_callerFrame (refs : BodyRefs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsNumerator : refs.wideNumerator.key ∉ other.storageKeys)
    (avoidsDenominator : refs.wideDenominator.key ∉ other.storageKeys) :
    ((roundingStep refs store).1).read other = store.read other := by
  unfold roundingStep
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsDenominator,
    correction_frame _ _ _ _ avoidsNumerator,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsNumerator]

/-- Actual prepared operands become precisely the positive or negative nearest-division formula. -/
theorem rounding_values (refs : BodyRefs ctx width) (separation : Separation refs)
    (store : Store ctx) (magnitude denominator : Nat) (negative : Bool)
    (numeratorValue : (store.read (writeInput refs.wideNumerator)).toNat = 2 * magnitude)
    (denominatorValue : (store.read (writeInput refs.wideDenominator)).toNat = denominator)
    (signValue : (store.read (writeInput refs.negative)).toBool = negative)
    (denominatorPositive : 0 < denominator)
    (dividendFits : 2 * magnitude + denominator < CShape.wordModulus (width + 1))
    (divisorFits : 2 * denominator < CShape.wordModulus (width + 1)) :
    (((roundingStep refs store).1).read (writeInput refs.wideNumerator)).toNat =
        (if negative then 2 * magnitude + denominator - 1 else 2 * magnitude + denominator) ∧
      (((roundingStep refs store).1).read (writeInput refs.wideDenominator)).toNat =
        2 * denominator ∧
      (((roundingStep refs store).1).read (writeInput refs.negative)).toBool = negative := by
  let added := store.applyOp (addDenominatorOp refs)
  let corrected := (correctionStep refs (added.read (writeInput refs.negative)) added).1
  have sumValue : (added.read (writeInput refs.wideNumerator)).toNat =
      2 * magnitude + denominator := by
    rw [add_read refs store (by rw [numeratorValue, denominatorValue]; exact dividendFits)]
    rw [numeratorValue, denominatorValue]
  have denominatorAdded : added.read (writeInput refs.wideDenominator) =
      store.read (writeInput refs.wideDenominator) :=
    read_other store (addDenominatorOp refs) refs.wideDenominator
      separation.wideNumeratorNeWideDenominator
  have signAdded : (added.read (writeInput refs.negative)).toBool = negative := by
    rw [read_other store (addDenominatorOp refs) refs.negative
      (Ne.symm separation.negativeNeWideNumerator)]
    exact signValue
  have correctedValue : (corrected.read (writeInput refs.wideNumerator)).toNat =
      (if negative then 2 * magnitude + denominator - 1 else 2 * magnitude + denominator) := by
    rw [correction_value refs _ added (by rw [sumValue]; omega), signAdded, sumValue]
  have denominatorCorrected : (corrected.read (writeInput refs.wideDenominator)).toNat =
      denominator := by
    rw [correction_frame refs _ added (writeInput refs.wideDenominator)
      (by simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using
        separation.wideNumeratorNeWideDenominator), denominatorAdded]
    exact denominatorValue
  have signCorrected : (corrected.read (writeInput refs.negative)).toBool = negative := by
    rw [correction_frame refs _ added (writeInput refs.negative)
      (by simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using
        Ne.symm separation.negativeNeWideNumerator)]
    exact signAdded
  change (((corrected.applyOp (doubleDenominatorOp refs)).read
      (writeInput refs.wideNumerator)).toNat = _) ∧
    (((corrected.applyOp (doubleDenominatorOp refs)).read
      (writeInput refs.wideDenominator)).toNat = _) ∧
    (((corrected.applyOp (doubleDenominatorOp refs)).read (writeInput refs.negative)).toBool = _)
  refine ⟨?_, ?_, ?_⟩
  · rw [read_other corrected (doubleDenominatorOp refs) refs.wideNumerator
      (Ne.symm separation.wideNumeratorNeWideDenominator)]
    exact correctedValue
  · exact (double_read corrected (writeInput refs.wideDenominator) refs.wideDenominator
      (by rw [denominatorCorrected]; exact divisorFits)).trans
        (congrArg (2 * ·) denominatorCorrected)
  · rw [read_other corrected (doubleDenominatorOp refs) refs.negative
      (Ne.symm separation.negativeNeWideDenominator)]
    exact signCorrected

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
