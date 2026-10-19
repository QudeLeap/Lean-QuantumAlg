/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.PMF
import all QuantumAlg.Util.PMF

/-!
# Joint success from marginal lower bounds

Two events may be arbitrarily correlated under the same distribution. Their
joint success loses at most the sum of their individual failure allowances.
-/

namespace QuantumAlg.PMF

/-- Two marginal success floors give a joint floor without any independence premise.
The floors lie in the unit interval because they are bounded by event probabilities. -/
public lemma jointEventProbability_ge_unionBound {Sample : Type}
    (distribution : PMF Sample) (first second : Sample → Prop)
    (firstFloor secondFloor : ENNReal)
    (firstBound : firstFloor ≤ distribution.toOuterMeasure {sample | first sample})
    (secondBound : secondFloor ≤ distribution.toOuterMeasure {sample | second sample}) :
    1 - ((1 - firstFloor) + (1 - secondFloor)) ≤
      distribution.toOuterMeasure {sample | first sample ∧ second sample} := by
  classical
  have failureBound (event : Sample → Prop) (floor : ENNReal)
      (success : floor ≤ distribution.toOuterMeasure {sample | event sample}) :
      distribution.toOuterMeasure {sample | ¬ event sample} ≤ 1 - floor := by
    rw [eventProbability_eq_one_sub_complement distribution (fun sample => ¬ event sample)]
    simpa only [not_not] using tsub_le_tsub_left success 1
  rw [eventProbability_eq_one_sub_complement distribution
    (fun sample => first sample ∧ second sample)]
  apply tsub_le_tsub_left
  calc
    distribution.toOuterMeasure {sample | ¬ (first sample ∧ second sample)} =
        distribution.toOuterMeasure
          ({sample | ¬ first sample} ∪ {sample | ¬ second sample}) := by
      congr 1
      ext sample
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      exact not_and_or
    _ ≤ distribution.toOuterMeasure {sample | ¬ first sample} +
        distribution.toOuterMeasure {sample | ¬ second sample} :=
      MeasureTheory.measure_union_le _ _
    _ ≤ (1 - firstFloor) + (1 - secondFloor) :=
      add_le_add (failureBound first firstFloor firstBound)
        (failureBound second secondFloor secondBound)

/-- The same bound applies to events stated on the two marginals of one joint PMF. -/
public lemma pairedEventProbability_ge_unionBound {Left Right : Type}
    (distribution : PMF (Left × Right)) (first : Left → Prop) (second : Right → Prop)
    (firstFloor secondFloor : ENNReal)
    (firstBound : firstFloor ≤
      (distribution.map Prod.fst).toOuterMeasure {value | first value})
    (secondBound : secondFloor ≤
      (distribution.map Prod.snd).toOuterMeasure {value | second value}) :
    1 - ((1 - firstFloor) + (1 - secondFloor)) ≤
      distribution.toOuterMeasure {pair | first pair.1 ∧ second pair.2} := by
  apply jointEventProbability_ge_unionBound distribution
    (fun pair => first pair.1) (fun pair => second pair.2) firstFloor secondFloor
  · simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using firstBound
  · simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using secondBound

end QuantumAlg.PMF
