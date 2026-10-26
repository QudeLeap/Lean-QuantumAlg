/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import Mathlib.Tactic

/-!
# Commutation of complete Jordan–Wigner strings

Parity overlap is counted at endpoints; overlapping Z tails are permitted.
-/

public section
namespace QuantumAlg.JordanWigner

/-- The XX and YY strings of a distinct hopping bond commute. -/
lemma hoppingString_xy_commute {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    PauliString.Commute (hoppingString p q .x) (hoppingString p q .y) := by
  have hpoint : ∀ j : Fin n,
      (if PauliLetter.anticommutes (hoppingString p q .x j) (hoppingString p q .y j)
        then 1 else 0 : ℕ) = (if j = p then 1 else 0) + (if j = q then 1 else 0) := by
    intro j
    simp only [hoppingString]
    split_ifs <;> simp_all [PauliLetter.anticommutes]
  simp only [PauliString.Commute, PauliString.anticommutingCount, hpoint,
    Finset.sum_add_distrib]
  simp

set_option maxHeartbeats 1600000 in
-- The finite endpoint-order split has four endpoint positions and two flavors.
/-- Every pair of strings belonging to disjoint bonds commutes, even when the
parity intervals overlap. -/
lemma hoppingString_commute_disjoint {n : ℕ} (p q r s : Fin n)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (a b : PauliLetter) (ha : a = .x ∨ a = .y) (hb : b = .x ∨ b = .y) :
    PauliString.Commute (hoppingString p q a) (hoppingString r s b) := by
  let B (u v j : Fin n) : ℕ := if min u v < j ∧ j < max u v then 1 else 0
  have hpoint : ∀ j : Fin n,
      (if PauliLetter.anticommutes (hoppingString p q a j) (hoppingString r s b j)
        then 1 else 0 : ℕ) =
      (if j = p then B r s p else 0) + (if j = q then B r s q else 0) +
      (if j = r then B p q r else 0) + (if j = s then B p q s else 0) := by
    intro j
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      by_cases hjp : j = p <;> by_cases hjq : j = q <;>
      by_cases hjr : j = r <;> by_cases hjs : j = s <;>
      simp_all [hoppingString, B, PauliLetter.anticommutes] <;>
      split_ifs <;> simp_all <;> omega
  have hcount : PauliString.anticommutingCount (hoppingString p q a)
      (hoppingString r s b) = B r s p + B r s q + B p q r + B p q s := by
    simp only [PauliString.anticommutingCount, hpoint, Finset.sum_add_distrib]
    simp
  rw [PauliString.Commute, hcount]
  simp only [B]
  split_ifs <;> simp_all only [min_lt_iff, lt_max_iff, Fin.lt_def, ne_eq, Fin.ext_iff] <;>
    norm_num <;> omega

end QuantumAlg.JordanWigner
