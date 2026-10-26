/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.PMF

/-!
# Monotonic pair-event probability under additional independent draws
-/

namespace QuantumAlg.PMF

noncomputable section

/-- An existing related pair remains present after one fresh draw is prepended. -/
lemma hasPair_cons_of_tail {Sample : Type} (relation : Sample × Sample → Prop)
    (head : Sample) (tail : List Sample) (related : HasPair relation tail) :
    HasPair relation (head :: tail) :=
  (hasPair_cons relation head tail).mpr (Or.inr related)

/-- More independent draws cannot lower the probability of containing a related pair. -/
lemma independentReplicate_hasPairProbability_mono {Sample : Type}
    (distribution : PMF Sample) (relation : Sample × Sample → Prop) :
    Monotone (fun count =>
      (independentReplicate distribution count).toOuterMeasure
        {samples | HasPair relation samples}) := by
  classical
  apply monotone_nat_of_le_succ
  intro count
  rw [independentReplicate, PMF.toOuterMeasure_bind_apply]
  calc
    (independentReplicate distribution count).toOuterMeasure
        {samples | HasPair relation samples} =
        ∑' head, distribution head *
          (independentReplicate distribution count).toOuterMeasure
            {samples | HasPair relation samples} := by
      rw [ENNReal.tsum_mul_right, distribution.tsum_coe, one_mul]
    _ ≤ ∑' head, distribution head *
        ((independentReplicate distribution count).map (List.cons head)).toOuterMeasure
          {samples | HasPair relation samples} := by
      apply ENNReal.tsum_le_tsum
      intro head
      apply mul_le_mul_right
      rw [PMF.toOuterMeasure_map_apply]
      apply PMF.toOuterMeasure_mono
      intro samples related
      exact hasPair_cons_of_tail relation head samples related.1

end

end QuantumAlg.PMF
