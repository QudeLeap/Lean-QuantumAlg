/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exact binomial-tail arithmetic

This module contains quantum-independent finite-probability calculations used
by repeated-sampling algorithms.  The statements are over exact rationals;
algorithm modules separately prove that their run-derived event masses satisfy
the hypotheses represented by these formulas.
-/

section

namespace QuantumAlg
namespace BinomialTail

/-- Probability that sixteen Bernoulli trials contain at most one success,
written in terms of the one-trial failure probability `q`. -/
def atMostOneOfSixteenFailure (q : Real) : Real :=
  q ^ 16 + 16 * (1 - q) * q ^ 15

/-- The at-most-one failure polynomial is monotone on the probability interval
`[0,1]`.  Its derivative is `240 q^14 (1-q)`, so increasing the one-trial
failure probability can only increase the batch failure probability. -/
lemma atMostOneOfSixteenFailure_monotoneOn :
    MonotoneOn atMostOneOfSixteenFailure (Set.Icc 0 1) := by
  have hderiv (q : Real) :
      HasDerivAt atMostOneOfSixteenFailure
        (240 * q ^ 14 * (1 - q)) q := by
    unfold atMostOneOfSixteenFailure
    convert!
      ((hasDerivAt_id q).pow 16).add
        (((hasDerivAt_const q (16 : Real)).mul
          ((hasDerivAt_const q (1 : Real)).sub (hasDerivAt_id q))).mul
            ((hasDerivAt_id q).pow 15)) using 1
    all_goals simp only [id_eq, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    all_goals ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : Real) 1)
  · unfold atMostOneOfSixteenFailure
    fun_prop
  · intro q _hq
    exact (hderiv q).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    rw [(hderiv q).deriv]
    rcases hq with ⟨hq0, hq1⟩
    positivity

/-- If one-trial failure is at most `7/8`, the exact at-most-one failure of a
sixteen-sample batch is bounded by its value at `7/8`. -/
lemma atMostOneOfSixteenFailure_le_atSevenEighths
    {q : Real} (hq0 : 0 ≤ q) (hq : q ≤ 7 / 8) :
    atMostOneOfSixteenFailure q ≤
      atMostOneOfSixteenFailure (7 / 8) := by
  exact atMostOneOfSixteenFailure_monotoneOn
    ⟨hq0, hq.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ hq

lemma atMostOneOfSixteenFailure_atSevenEighths :
    atMostOneOfSixteenFailure (7 / 8) =
      (109193914728689 / 281474976710656 : Real) := by
  norm_num [atMostOneOfSixteenFailure]

/-- Exact probability that sixteen independent Bernoulli trials of probability
`1/8` contain at least two successes. -/
def atLeastTwoOfSixteenAtOneEighth : ℚ :=
  1 - (7 / 8) ^ 16 - 16 * (1 / 8) * (7 / 8) ^ 15

lemma atLeastTwoOfSixteenAtOneEighth_eq :
    atLeastTwoOfSixteenAtOneEighth =
      172281061981967 / 281474976710656 := by
  norm_num [atLeastTwoOfSixteenAtOneEighth]

/-- Conservative batch floor after subtracting a `1/8` recovery-failure
budget from the probability of obtaining at least two good samples. -/
def sixteenSampleBatchFloor : ℚ :=
  atLeastTwoOfSixteenAtOneEighth - 1 / 8

lemma sixteenSampleBatchFloor_eq :
    sixteenSampleBatchFloor =
      137096689893135 / 281474976710656 := by
  norm_num [sixteenSampleBatchFloor, atLeastTwoOfSixteenAtOneEighth]

lemma sixteenSampleBatchFloor_pos : 0 < sixteenSampleBatchFloor := by
  norm_num [sixteenSampleBatchFloor, atLeastTwoOfSixteenAtOneEighth]

end BinomialTail
end QuantumAlg

end
