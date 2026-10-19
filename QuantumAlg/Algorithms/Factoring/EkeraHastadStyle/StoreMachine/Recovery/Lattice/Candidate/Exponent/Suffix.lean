/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent.Frames

/-!
# Actual candidate-exponent suffix checks
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original seven-instruction suffix's exact exponent and four Boolean outputs. -/
structure SuffixOutcome (refs : Refs ctx width) (store : Store ctx)
    (magnitude upper : Nat) (negative : Bool) : Prop where
  exponent : (store.read (writeInput refs.exponent)).toNat = magnitude
  positive : (store.read (writeInput refs.positive)).toBool = decide (magnitude ≠ 0)
  belowUpper : (store.read (writeInput refs.belowUpper)).toBool = decide (magnitude < upper)
  nonnegative : (store.read (writeInput refs.nonnegative)).toBool = !negative
  accepted : (store.read (writeInput refs.accepted)).toBool =
    ((decide (magnitude ≠ 0) && decide (magnitude < upper)) && !negative)

omit [BitWord.Selected model] in
/-- Actual stored values determine every original suffix check and the final acceptance bit. -/
lemma suffixInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (magnitude upper : Nat) (negative : Bool)
    (magnitudeValue : (store.read (writeInput refs.magnitude)).toNat = magnitude)
    (negativeValue : (store.read (writeInput refs.negative)).toBool = negative)
    (zeroValue : (store.read refs.zero).toNat = 0)
    (upperValue : (store.read refs.upperBound).toNat = upper) :
    SuffixOutcome refs (suffixStore refs store) magnitude upper negative := by
  let copied := store.applyOp (copyOp refs)
  let equalled := copied.applyOp (equalOp refs)
  let positive := equalled.applyOp (positiveOp refs)
  let below := positive.applyOp (belowOp refs)
  let nonnegative := below.applyOp (nonnegativeOp refs)
  let ranged := nonnegative.applyOp (rangeOp refs)
  let finished := ranged.applyOp (acceptedOp refs)
  have exponentAtCopy : (copied.read (writeInput refs.exponent)).toNat = magnitude := by
    change ((store.applyOp (copyOp refs)).read
      (.storage (copyOp refs).outputRef.toCStorageRef)).toNat = _
    rw [Store.read_applyOp_output]
    exact magnitudeValue
  have magnitudeAtEqual : copied.read (writeInput refs.magnitude) =
      store.read (writeInput refs.magnitude) :=
    (mutable_read_apply refs separation (copyOp refs) .exponent rfl
        refs.magnitude .magnitude rfl (by decide) store)
  have zeroAtEqual : copied.read refs.zero = store.read refs.zero :=
    (source_read_apply refs separation (copyOp refs) .exponent rfl .zero store)
  have equalValue : (equalled.read (writeInput refs.positive)).toBool = decide (magnitude = 0) := by
    change ((copied.applyOp (equalOp refs)).read
      (.storage (equalOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change decide ((copied.read (writeInput refs.magnitude)).toNat =
      (copied.read refs.zero).toNat) = _
    rw [magnitudeAtEqual, zeroAtEqual, magnitudeValue, zeroValue]
  have positiveValue : (positive.read (writeInput refs.positive)).toBool =
      decide (magnitude ≠ 0) := by
    change ((equalled.applyOp (positiveOp refs)).read
      (.storage (positiveOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change (Resource.BitOpcode.eval .not (equalled.read (writeInput refs.positive))).toBool = _
    rw [bitNotEval_toBool, equalValue]
    simp
  have magnitudeAtBelow : positive.read (writeInput refs.magnitude) =
      store.read (writeInput refs.magnitude) :=
    (mutable_read_apply refs separation (positiveOp refs) .positive rfl
        refs.magnitude .magnitude rfl (by decide) equalled).trans (
      (mutable_read_apply refs separation (equalOp refs) .positive rfl
        refs.magnitude .magnitude rfl (by decide) copied).trans (
      (mutable_read_apply refs separation (copyOp refs) .exponent rfl
        refs.magnitude .magnitude rfl (by decide) store)))
  have upperAtBelow : positive.read refs.upperBound = store.read refs.upperBound :=
    (source_read_apply refs separation (positiveOp refs) .positive rfl .upperBound equalled).trans (
      (source_read_apply refs separation (equalOp refs) .positive rfl .upperBound copied).trans (
      (source_read_apply refs separation (copyOp refs) .exponent rfl .upperBound store)))
  have belowValue : (below.read (writeInput refs.belowUpper)).toBool =
      decide (magnitude < upper) := by
    change ((positive.applyOp (belowOp refs)).read
      (.storage (belowOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change decide ((positive.read (writeInput refs.magnitude)).toNat <
      (positive.read refs.upperBound).toNat) = _
    rw [magnitudeAtBelow, upperAtBelow, magnitudeValue, upperValue]
  have negativeAtNot : below.read (writeInput refs.negative) =
      store.read (writeInput refs.negative) :=
    (mutable_read_apply refs separation (belowOp refs) .belowUpper rfl
        refs.negative .negative rfl (by decide) positive).trans (
      (mutable_read_apply refs separation (positiveOp refs) .positive rfl
        refs.negative .negative rfl (by decide) equalled).trans (
      (mutable_read_apply refs separation (equalOp refs) .positive rfl
        refs.negative .negative rfl (by decide) copied).trans (
      (mutable_read_apply refs separation (copyOp refs) .exponent rfl
        refs.negative .negative rfl (by decide) store))))
  have nonnegativeValue : (nonnegative.read (writeInput refs.nonnegative)).toBool = !negative := by
    change ((below.applyOp (nonnegativeOp refs)).read
      (.storage (nonnegativeOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change (Resource.BitOpcode.eval .not (below.read (writeInput refs.negative))).toBool = _
    rw [bitNotEval_toBool, negativeAtNot, negativeValue]
  have positiveAtAnd : nonnegative.read (writeInput refs.positive) =
      positive.read (writeInput refs.positive) :=
    (mutable_read_apply refs separation (nonnegativeOp refs) .nonnegative rfl
        refs.positive .positive rfl (by decide) below).trans (
      (mutable_read_apply refs separation (belowOp refs) .belowUpper rfl
        refs.positive .positive rfl (by decide) positive))
  have belowAtAnd : nonnegative.read (writeInput refs.belowUpper) =
      below.read (writeInput refs.belowUpper) :=
    (mutable_read_apply refs separation (nonnegativeOp refs) .nonnegative rfl
        refs.belowUpper .belowUpper rfl (by decide) below)
  have rangeValue : (ranged.read (writeInput refs.accepted)).toBool =
      (decide (magnitude ≠ 0) && decide (magnitude < upper)) := by
    change ((nonnegative.applyOp (rangeOp refs)).read
      (.storage (rangeOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change (Resource.BitOpcode.eval .and (.product (nonnegative.read (writeInput refs.positive))
      (nonnegative.read (writeInput refs.belowUpper)))).toBool = _
    rw [bitAndEval_toBool, positiveAtAnd, belowAtAnd, positiveValue, belowValue]
  have nonnegativeAtFinal : ranged.read (writeInput refs.nonnegative) =
      nonnegative.read (writeInput refs.nonnegative) :=
    (mutable_read_apply refs separation (rangeOp refs) .accepted rfl
        refs.nonnegative .nonnegative rfl (by decide) nonnegative)
  have acceptedValue : (finished.read (writeInput refs.accepted)).toBool =
      ((decide (magnitude ≠ 0) && decide (magnitude < upper)) && !negative) := by
    change ((ranged.applyOp (acceptedOp refs)).read
      (.storage (acceptedOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change (Resource.BitOpcode.eval .and (.product (ranged.read (writeInput refs.accepted))
      (ranged.read (writeInput refs.nonnegative)))).toBool = _
    rw [bitAndEval_toBool, nonnegativeAtFinal, rangeValue, nonnegativeValue]
  have exponentRetained : finished.read (writeInput refs.exponent) =
      copied.read (writeInput refs.exponent) :=
    (mutable_read_apply refs separation (acceptedOp refs) .accepted rfl
        refs.exponent .exponent rfl (by decide) ranged).trans (
      (mutable_read_apply refs separation (rangeOp refs) .accepted rfl
        refs.exponent .exponent rfl (by decide) nonnegative).trans (
      (mutable_read_apply refs separation (nonnegativeOp refs) .nonnegative rfl
        refs.exponent .exponent rfl (by decide) below).trans (
      (mutable_read_apply refs separation (belowOp refs) .belowUpper rfl
        refs.exponent .exponent rfl (by decide) positive).trans (
      (mutable_read_apply refs separation (positiveOp refs) .positive rfl
        refs.exponent .exponent rfl (by decide) equalled).trans (
      (mutable_read_apply refs separation (equalOp refs) .positive rfl
        refs.exponent .exponent rfl (by decide) copied))))))
  have positiveRetained : finished.read (writeInput refs.positive) =
      positive.read (writeInput refs.positive) :=
    (mutable_read_apply refs separation (acceptedOp refs) .accepted rfl
        refs.positive .positive rfl (by decide) ranged).trans (
      (mutable_read_apply refs separation (rangeOp refs) .accepted rfl
        refs.positive .positive rfl (by decide) nonnegative).trans (
      (mutable_read_apply refs separation (nonnegativeOp refs) .nonnegative rfl
        refs.positive .positive rfl (by decide) below).trans (
      (mutable_read_apply refs separation (belowOp refs) .belowUpper rfl
        refs.positive .positive rfl (by decide) positive))))
  have belowRetained : finished.read (writeInput refs.belowUpper) =
      below.read (writeInput refs.belowUpper) :=
    (mutable_read_apply refs separation (acceptedOp refs) .accepted rfl
        refs.belowUpper .belowUpper rfl (by decide) ranged).trans (
      (mutable_read_apply refs separation (rangeOp refs) .accepted rfl
        refs.belowUpper .belowUpper rfl (by decide) nonnegative).trans (
      (mutable_read_apply refs separation (nonnegativeOp refs) .nonnegative rfl
        refs.belowUpper .belowUpper rfl (by decide) below)))
  have nonnegativeRetained : finished.read (writeInput refs.nonnegative) =
      nonnegative.read (writeInput refs.nonnegative) :=
    (mutable_read_apply refs separation (acceptedOp refs) .accepted rfl
        refs.nonnegative .nonnegative rfl (by decide) ranged).trans (
      (mutable_read_apply refs separation (rangeOp refs) .accepted rfl
        refs.nonnegative .nonnegative rfl (by decide) nonnegative))
  refine ⟨?_, ?_, ?_, ?_, acceptedValue⟩
  · change (finished.read (writeInput refs.exponent)).toNat = _
    rw [exponentRetained, exponentAtCopy]
  · change (finished.read (writeInput refs.positive)).toBool = _
    rw [positiveRetained, positiveValue]
  · change (finished.read (writeInput refs.belowUpper)).toBool = _
    rw [belowRetained, belowValue]
  · change (finished.read (writeInput refs.nonnegative)).toBool = _
    rw [nonnegativeRetained, nonnegativeValue]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
