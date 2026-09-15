/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.PMF

/-!
# Stability of independently repeated PMF events

This module lifts a one-draw additive event bound through a fixed number of
independent repetitions.  The loss is linear in the repetition count; no
coupling object or detached probability model is introduced.
-/

section

namespace QuantumAlg
namespace PMF

noncomputable section

/-- Taking complements reverses a one-sided additive bound inside the unit
interval. -/
theorem one_tsub_le_one_tsub_add {left right error : ENNReal}
    (bound : left ≤ right + error) :
    1 - right ≤ 1 - left + error := by
  rw [tsub_le_iff_right]
  calc
    1 ≤ 1 - left + left := le_tsub_add
    _ ≤ 1 - left + (right + error) := by gcongr
    _ = (1 - left + error) + right := by ac_rfl

/-- On the unit interval, a one-step additive perturbation grows at most
linearly under natural powers. -/
theorem pow_le_pow_add_nat_mul {left right error : ENNReal}
    (left_le_one : left ≤ 1) (right_le_one : right ≤ 1)
    (bound : left ≤ right + error) (count : Nat) :
    left ^ count ≤ right ^ count + (count : ENNReal) * error := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      calc
        left ^ (count + 1) = left ^ count * left := by rw [pow_succ]
        _ ≤ (right ^ count + (count : ENNReal) * error) * left :=
          mul_le_mul_left inductionHypothesis left
        _ = right ^ count * left + (count : ENNReal) * error * left := by
          rw [add_mul]
        _ ≤ right ^ count * left + (count : ENNReal) * error := by
          have errorBound :
              (count : ENNReal) * error * left ≤
                (count : ENNReal) * error * 1 :=
            mul_le_mul_right left_le_one _
          simpa using add_le_add (le_refl (right ^ count * left)) errorBound
        _ ≤ right ^ count * (right + error) + (count : ENNReal) * error := by
          have leadingBound :
              right ^ count * left ≤ right ^ count * (right + error) :=
            mul_le_mul_right bound _
          exact add_le_add leadingBound (le_refl _)
        _ = right ^ (count + 1) + right ^ count * error +
              (count : ENNReal) * error := by
          rw [mul_add, pow_succ]
        _ ≤ right ^ (count + 1) + error + (count : ENNReal) * error := by
          have errorBound : right ^ count * error ≤ error := by
            have powerBound : right ^ count ≤ 1 :=
              pow_le_one₀ (by positivity) right_le_one
            have productBound : right ^ count * error ≤ 1 * error :=
              mul_le_mul_left powerBound error
            simpa using productBound
          exact add_le_add
            (add_le_add (le_refl (right ^ (count + 1))) errorBound)
            (le_refl _)
        _ = right ^ (count + 1) + ((count + 1 : Nat) : ENNReal) * error := by
          push_cast
          ring

/-- If every one-draw event under `ideal` is bounded by the corresponding
event under `actual` plus `error`, then the probability of seeing the event at
least once in `count` independent draws obeys the same bound with loss
`count * error`. -/
theorem independentReplicate_successProbability_le_add
    {Sample : Type} (ideal actual : PMF Sample) (event : Sample → Prop)
    (count : Nat) (error : ENNReal)
    (oneDraw :
      ideal.toOuterMeasure {sample | event sample} ≤
        actual.toOuterMeasure {sample | event sample} + error) :
    (independentReplicate ideal count).toOuterMeasure
        {samples | ContainsEvent event samples} ≤
      (independentReplicate actual count).toOuterMeasure
          {samples | ContainsEvent event samples} +
        (count : ENNReal) * error := by
  rw [independentReplicate_successProbability_eq,
    independentReplicate_successProbability_eq]
  have idealComplement :
      ideal.toOuterMeasure {sample | ¬ event sample} =
        1 - ideal.toOuterMeasure {sample | event sample} := by
    rw [eventProbability_eq_one_sub_complement ideal
      (fun sample => ¬ event sample)]
    congr 2
    ext sample
    simp
  have actualComplement :
      actual.toOuterMeasure {sample | ¬ event sample} =
        1 - actual.toOuterMeasure {sample | event sample} := by
    rw [eventProbability_eq_one_sub_complement actual
      (fun sample => ¬ event sample)]
    congr 2
    ext sample
    simp
  rw [idealComplement, actualComplement]
  apply one_tsub_le_one_tsub_add
  apply pow_le_pow_add_nat_mul
  · exact tsub_le_self
  · exact tsub_le_self
  · exact one_tsub_le_one_tsub_add oneDraw

/-- The same independent-repetition perturbation bound with the sample count
retained in the result type. -/
theorem independentReplicateVector_successProbability_le_add
    {Sample : Type} (ideal actual : PMF Sample) (event : Sample → Prop)
    (count : Nat) (error : ENNReal)
    (oneDraw :
      ideal.toOuterMeasure {sample | event sample} ≤
        actual.toOuterMeasure {sample | event sample} + error) :
    (independentReplicateVector ideal count).toOuterMeasure
        {samples | ContainsEvent event samples.toList} ≤
      (independentReplicateVector actual count).toOuterMeasure
          {samples | ContainsEvent event samples.toList} +
        (count : ENNReal) * error := by
  calc
    (independentReplicateVector ideal count).toOuterMeasure
        {samples | ContainsEvent event samples.toList} =
      ((independentReplicateVector ideal count).map List.Vector.toList).toOuterMeasure
        {samples | ContainsEvent event samples} := by
          rw [PMF.toOuterMeasure_map_apply]
          congr 1
    _ = (independentReplicate ideal count).toOuterMeasure
        {samples | ContainsEvent event samples} := by
          rw [independentReplicateVector_toList]
    _ ≤ (independentReplicate actual count).toOuterMeasure
          {samples | ContainsEvent event samples} +
        (count : ENNReal) * error :=
      independentReplicate_successProbability_le_add
        ideal actual event count error oneDraw
    _ = ((independentReplicateVector actual count).map List.Vector.toList).toOuterMeasure
          {samples | ContainsEvent event samples} +
        (count : ENNReal) * error := by
          rw [independentReplicateVector_toList]
    _ = (independentReplicateVector actual count).toOuterMeasure
          {samples | ContainsEvent event samples.toList} +
        (count : ENNReal) * error := by
          rw [PMF.toOuterMeasure_map_apply]
          congr 2

end

end PMF
end QuantumAlg

end
