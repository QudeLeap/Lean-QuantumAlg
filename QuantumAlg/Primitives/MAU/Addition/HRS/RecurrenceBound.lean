/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Split
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Upper bound for the exact HRS balanced recurrence

This quantum-free lemma bounds a numerical recurrence on the actual
ceiling/floor split [HRS16, paper.tex:232-260]. Its recurrence premise must
be proved from the executed circuit before the result can serve as a
resource contract. It introduces no circuit or independent resource witness.
-/

namespace QuantumAlg.MAU.Addition.HRS

/-- A non-base input loses exactly one ceiling-logarithm level in its larger half. -/
lemma hrsSplit_clog (width : Nat) (h : 2 ≤ width) :
    Nat.clog 2 width = Nat.clog 2 (lowWidth width) + 1 := by
  have hlog := Nat.clog_of_two_le (b := 2) (n := width) (by decide) h
  rw [show width + 2 - 1 = width + 1 by omega] at hlog
  exact hlog

/-- The actual constant-dependent split recurrence has an explicit logarithmic bound. -/
lemma hrsBalancedRecurrence_bound
    (cost : (width : Nat) → Fin (2 ^ width) → Nat)
    (base : ∀ width, width ≤ 1 → ∀ constant, cost width constant ≤ width)
    (step : ∀ width, 2 ≤ width → ∀ constant,
      cost width constant ≤ 39 * width +
        cost (lowWidth width) ((splitWord width) constant).1 +
        cost (highWidth width) ((splitWord width) constant).2) :
    ∀ width constant, cost width constant ≤ width * (39 * Nat.clog 2 width + 1) := by
  intro width
  induction width using Nat.strong_induction_on with
  | h width ih =>
      intro constant
      by_cases hbase : width ≤ 1
      · have hbound := base width hbase constant
        simpa only [Nat.clog_of_right_le_one hbase, Nat.mul_zero, Nat.zero_add,
          Nat.mul_one] using hbound
      · have htwo : 2 ≤ width := by omega
        have hdecrease := hrsSplit_decreases width htwo
        have hlow := ih (lowWidth width) hdecrease.1 ((splitWord width) constant).1
        have hhigh := ih (highWidth width) hdecrease.2 ((splitWord width) constant).2
        have hstep := step width htwo constant
        have hlog : Nat.clog 2 (highWidth width) ≤ Nat.clog 2 (lowWidth width) :=
          Nat.clog_mono_right 2 (hrsSplit_capacity width).2.1
        have hhigh' : highWidth width * (39 * Nat.clog 2 (highWidth width) + 1) ≤
            highWidth width * (39 * Nat.clog 2 (lowWidth width) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [hrsSplit_clog width htwo]
        calc
          cost width constant ≤ 39 * width +
              lowWidth width * (39 * Nat.clog 2 (lowWidth width) + 1) +
              highWidth width * (39 * Nat.clog 2 (lowWidth width) + 1) := by omega
          _ = 39 * width + (lowWidth width + highWidth width) *
              (39 * Nat.clog 2 (lowWidth width) + 1) := by ring
          _ = width * (39 * (Nat.clog 2 (lowWidth width) + 1) + 1) := by
            rw [hrsSplit_width_sum]
            ring

end QuantumAlg.MAU.Addition.HRS
