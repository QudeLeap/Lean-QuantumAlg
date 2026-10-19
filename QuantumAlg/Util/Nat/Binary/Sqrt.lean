/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Sqrt
import Lean.Elab.Tactic.Omega

/-!
# Exact descending-bit refinement of the natural square root

One step tests the square of the old lower estimate plus its current binary
increment. The remaining interval halves at every step. The finite-width
capacity bound also propagates, so an actual word implementation can use
the same addition and full-width square without an overflow precondition
on its caller. These statements have no execution or storage dependencies.
-/

namespace QuantumAlg.Nat.BinarySqrt

/-- The same candidate-square comparison used by one binary refinement. -/
def refine (input half root : Nat) : Nat :=
  if (root + half) * (root + half) ≤ input then root + half else root

/-- Execute the exact descending binary increments, including the empty iteration. -/
def run (input : Nat) : Nat → Nat → Nat
  | 0, root => root
  | remaining + 1, root => run input remaining (refine input (2 ^ remaining) root)

/-- The remaining binary interval contains exactly the sought square root. -/
structure Interval (input remaining root : Nat) : Prop where
  /-- The current root estimate does not overshoot the input square. -/
  lower : root * root ≤ input
  /-- The upper endpoint is strictly above the square root. -/
  upper : input < (root + 2 ^ remaining) * (root + 2 ^ remaining)

/-- The literal too-large test chooses the same candidate as the non-strict square test. -/
lemma refine_eq_tooLarge (input half root : Nat) :
    refine input half root =
      if input < (root + half) * (root + half) then root else root + half := by
  unfold refine
  by_cases smaller : input < (root + half) * (root + half)
  · rw [if_pos smaller, if_neg (Nat.not_le.mpr smaller)]
  · rw [if_neg smaller, if_pos (Nat.le_of_not_gt smaller)]

/-- One literal refinement halves the exact remaining square-root interval. -/
lemma refine_interval {input remaining root : Nat}
    (interval : Interval input (remaining + 1) root) :
    Interval input remaining (refine input (2 ^ remaining) root) := by
  have doubled : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    rw [Nat.pow_succ]
    omega
  by_cases accepted : (root + 2 ^ remaining) * (root + 2 ^ remaining) ≤ input
  · rw [refine, if_pos accepted]
    refine ⟨accepted, ?_⟩
    have endpoint : root + 2 ^ remaining + 2 ^ remaining = root + 2 ^ (remaining + 1) :=
      by omega
    rw [endpoint]
    exact interval.upper
  · rw [refine, if_neg accepted]
    exact ⟨interval.lower, Nat.lt_of_not_ge accepted⟩

/-- Every tested midpoint fits the declared word whenever the old interval endpoint fits. -/
lemma midpoint_lt_capacity {remaining root capacity : Nat}
    (bounded : root + 2 ^ (remaining + 1) ≤ capacity) :
    root + 2 ^ remaining < capacity := by
  have positive : 0 < 2 ^ remaining := Nat.two_pow_pos remaining
  have doubled : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    rw [Nat.pow_succ]
    omega
  omega

/-- The accepted or rejected refinement keeps the smaller interval inside the same capacity. -/
lemma refine_capacity {input remaining root capacity : Nat}
    (bounded : root + 2 ^ (remaining + 1) ≤ capacity) :
    refine input (2 ^ remaining) root + 2 ^ remaining ≤ capacity := by
  have positive := Nat.two_pow_pos remaining
  have doubled : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    rw [Nat.pow_succ]
    omega
  unfold refine
  split <;> omega

/-- No remaining bit leaves a unit interval, which characterizes the exact natural square root. -/
lemma Interval.finished {input root : Nat} (interval : Interval input 0 root) :
    root = Nat.sqrt input := by
  apply Nat.eq_sqrt.mpr
  exact ⟨interval.lower, by simpa only [Nat.pow_zero] using interval.upper⟩

/-- The complete descending refinement returns the exact square root of its original interval. -/
lemma run_eq_sqrt {input remaining root : Nat} (interval : Interval input remaining root) :
    run input remaining root = Nat.sqrt input := by
  induction remaining generalizing root with
  | zero => exact interval.finished
  | succ remaining inductionHypothesis =>
      exact inductionHypothesis (refine_interval interval)

/-- The zero estimate covers every value of the declared input word, including width zero. -/
lemma initial_interval {input width : Nat} (bounded : input < 2 ^ width) :
    Interval input width 0 := by
  refine ⟨Nat.zero_le _, ?_⟩
  simpa only [Nat.zero_add] using Nat.lt_of_lt_of_le bounded (Nat.le_mul_self (2 ^ width))

/-- A fixed number of actual refinement steps suffices for every input word of that width. -/
lemma run_zero_eq_sqrt {input width : Nat} (bounded : input < 2 ^ width) :
    run input width 0 = Nat.sqrt input :=
  run_eq_sqrt (initial_interval bounded)

end QuantumAlg.Nat.BinarySqrt
