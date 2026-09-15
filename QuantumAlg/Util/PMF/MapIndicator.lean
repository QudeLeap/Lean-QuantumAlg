/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.PMF
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Complex.BigOperators

/-!
# The finite original fiber of one mapped PMF point

A characteristic sum over a finite original sample space gives the point
probability of its ordinary deterministic pushforward. The result space need
not be finite. The identity uses the existing PMF map alone.
-/

namespace QuantumAlg.PMF

noncomputable section

/-- An exact characteristic weight sums precisely the original fiber of the mapped point. -/
theorem sum_toReal_map_indicator {A B : Type} [Fintype A] [DecidableEq B]
    (distribution : PMF A) (map : A → B) (selected : B) :
    (∑ original : A, ((distribution original).toReal : ℂ) *
      (if map original = selected then 1 else 0)) =
      ((distribution.map map selected).toReal : ℂ) := by
  have point : (distribution.map map selected).toReal =
      ∑ original : A, if selected = map original then (distribution original).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro original _
      by_cases matching : selected = map original
      · simp only [if_pos matching]
      · simp only [if_neg matching, ENNReal.toReal_zero]
    · intro original _
      split
      · exact distribution.apply_ne_top original
      · exact ENNReal.zero_ne_top
  rw [point, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro original _
  by_cases matching : map original = selected
  · simp only [matching, if_true, mul_one]
  · simp only [if_neg matching, if_neg (Ne.symm matching), Complex.ofReal_zero, mul_zero]

end

end QuantumAlg.PMF
