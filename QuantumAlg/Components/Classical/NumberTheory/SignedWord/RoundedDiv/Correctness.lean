/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Rounding
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Finish

/-!
# Signed nearest-division correctness on actual stores

The caller's positive-denominator and separation contract suffices with arbitrary
initial scratch. Every operand and branch flag below comes from the actual
chronological store writes of the circuit.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual signed nearest division preserves all caller reads outside its six mutable cells. -/
theorem body_callerFrame (refs : BodyRefs ctx width) (store : Store ctx) :
    CallerFrame refs store (bodyStep refs store).1 := by
  intro shape other avoids
  unfold bodyStep
  rw [finish_callerFrame _ _ _ (avoids _ (by simp [mutableKeys])),
    Store.read_applyOp_of_not_mem_storageKeys _ _ _
      (avoids refs.division.key (by simp [mutableKeys])),
    rounding_callerFrame _ _ _ (avoids _ (by simp [mutableKeys]))
      (avoids _ (by simp [mutableKeys])),
    prepare_callerFrame _ _ _ (avoids _ (by simp [mutableKeys]))
      (avoids _ (by simp [mutableKeys])) (avoids _ (by simp [mutableKeys]))
      (avoids _ (by simp [mutableKeys]))]

/-- The actual final output represents nearest-integer division of the original signed input. -/
theorem body_outputRepresents (refs : BodyRefs ctx width) (separation : Separation refs)
    (store : Store ctx) (widthPositive : 0 < width)
    (denominatorPositive : 0 < (store.read refs.denominator).toNat) :
    RawSignedRepresents ((bodyStep refs store).1.read (writeInput refs.output))
      (QuantumAlg.NumberTheory.nearestIntegerCoefficient
        (decodeRawSignedWord (store.read refs.numerator))
        ((store.read refs.denominator).toNat : Int)) := by
  let prepared := (prepareStep refs store).1
  let rounded := (roundingStep refs prepared).1
  let divided := rounded.applyOp (divideOp refs)
  obtain ⟨numeratorPrepared, denominatorPrepared, signPrepared⟩ :=
    prepare_values refs separation store widthPositive
  obtain ⟨numeratorRounded, denominatorRounded, signRounded⟩ :=
    rounding_values refs separation prepared (rawMagnitude (store.read refs.numerator))
      (store.read refs.denominator).toNat (rawIsNegative (store.read refs.numerator))
      numeratorPrepared denominatorPrepared signPrepared denominatorPositive
      (roundedDividend_fits widthPositive _ _) (doubledDenominator_fits _)
  have signDivided : (divided.read (writeInput refs.negative)).toBool =
      rawIsNegative (store.read refs.numerator) := by
    rw [read_other rounded (divideOp refs) refs.negative (Ne.symm separation.negativeNeDivision)]
    exact signRounded
  have output := finish_represents refs divided (Ne.symm separation.negativeNeOutput)
  rw [signDivided, divide_quotient, numeratorRounded, denominatorRounded] at output
  change RawSignedRepresents ((finishStep refs divided).1.read (writeInput refs.output)) _
  rw [decodeRawSignedWord_eq_signedMagnitude widthPositive]
  cases flag : rawIsNegative (store.read refs.numerator) with
  | false =>
      simp only [flag, Bool.false_eq_true, if_false] at output ⊢
      rw [nearestIntegerCoefficient_ofNat_formula _ _ denominatorPositive]
      exact output
  | true =>
      have magnitudePositive : 0 < rawMagnitude (store.read refs.numerator) := by
        have bounded : (store.read refs.numerator).toNat < CShape.wordModulus width :=
          (store.read refs.numerator).toNat_lt
        simp only [rawMagnitude, flag, if_true]
        omega
      simp only [flag, if_true] at output ⊢
      rw [nearestIntegerCoefficient_neg_ofNat_formula _ _ magnitudePositive denominatorPositive]
      exact output

/-- Raw represented inputs specialize the actual-store result to the caller's integer values. -/
theorem body_outputRepresents_of_raw (refs : BodyRefs ctx width) (separation : Separation refs)
    (store : Store ctx) (numeratorValue : Int) (denominatorValue : Nat)
    (widthPositive : 0 < width) (denominatorPositive : 0 < denominatorValue)
    (numeratorRepresents : RawSignedRepresents (store.read refs.numerator) numeratorValue)
    (numeratorRange :
      ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width numeratorValue)
    (denominatorRepresents :
      RawSignedRepresents (store.read refs.denominator) (denominatorValue : Int))
    (denominatorFits : denominatorValue < CShape.wordModulus width) :
    RawSignedRepresents ((bodyStep refs store).1.read (writeInput refs.output))
      (QuantumAlg.NumberTheory.nearestIntegerCoefficient
        numeratorValue (denominatorValue : Int)) := by
  have numeratorDecoded := rawSignedRepresents_decode_eq _ _ widthPositive
    numeratorRepresents numeratorRange
  have denominatorDecoded := rawSignedRepresents_toNat_eq_of_lt _
    denominatorRepresents denominatorFits
  have actual := body_outputRepresents refs separation store widthPositive
    (by rw [denominatorDecoded]; exact denominatorPositive)
  rw [numeratorDecoded, denominatorDecoded] at actual
  exact actual

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
