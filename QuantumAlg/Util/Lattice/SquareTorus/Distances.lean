/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Lattice.SquareTorus.Edges
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Util.Lattice.SquareTorus.Edges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Distances in the periodic row-snake ordering

The sum includes horizontal and vertical wrap bonds. These exact index-distance
identities determine the support lengths of Jordan-Wigner hopping strings.
-/

@[expose] public section

namespace SquareTorus

/-- Ordinary horizontal neighbours are adjacent; a row wrap has distance L-1. -/
lemma snake_horizontal_distance {L : ℕ} (p : Site L) :
    Nat.dist (snakeIndex p).val (snakeIndex (right p)).val =
      if p.2.val + 1 < L then 1 else L - 1 := by
  rcases p with ⟨r, c⟩
  have := r.isLt
  have := c.isLt
  have := c.pos
  simp only [right, snakeIndex_val, next_val, Nat.dist]
  split_ifs <;> omega

lemma sum_snake_horizontal_row {L : ℕ} (r : Fin L) :
    (∑ c : Fin L, Nat.dist (snakeIndex (r, c)).val (snakeIndex (right (r, c))).val) =
      2 * (L - 1) := by
  cases L with
  | zero => exact Fin.elim0 r
  | succ k =>
    simp_rw [snake_horizontal_distance]
    rw [Fin.sum_univ_castSucc]
    simp [two_mul]

lemma sum_snake_horizontal_distance {L : ℕ} :
    (∑ p : Site L, Nat.dist (snakeIndex p).val (snakeIndex (right p)).val) =
      2 * L * (L - 1) := by
  simp only [Fintype.sum_prod_type, sum_snake_horizontal_row,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ac_rfl

/-- Reversing a row leaves the sum of its column offsets unchanged. -/
lemma sum_snake_column {L : ℕ} (r : Fin L) :
    (∑ c : Fin L, (snakeColumn r c).val) = ∑ c : Fin L, c.val := by
  by_cases h : r.val % 2 = 0
  · simp [snakeColumn, h]
  · simpa only [snakeColumn, if_neg h, Fin.revPerm_apply] using
      Equiv.sum_comp (Fin.revPerm (n := L)) (fun c => c.val)

lemma sum_snake_index_row {L : ℕ} (r : Fin L) :
    (∑ c : Fin L, (snakeIndex (r, c)).val) = L * (L * r.val) + ∑ c : Fin L, c.val := by
  simp only [snakeIndex_val_column, Finset.sum_add_distrib, sum_snake_column,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

lemma snake_index_row_lt {L : ℕ} {r s : Fin L} (hrs : r < s) (c d : Fin L) :
    snakeIndex (r, c) < snakeIndex (s, d) := by
  change (snakeColumn r c).val + L * r.val < (snakeColumn s d).val + L * s.val
  have hc := (snakeColumn r c).isLt
  have hr : r.val + 1 ≤ s.val := hrs
  have hmul := Nat.mul_le_mul_left L hr
  nlinarith

/-- Every nonwrapping row transition has the same total index distance. -/
lemma sum_snake_vertical_row_of_lt {L : ℕ} (r : Fin L) (h : r.val + 1 < L) :
    (∑ c : Fin L, Nat.dist (snakeIndex (r, c)).val (snakeIndex (down (r, c))).val) =
      L ^ 2 := by
  have hr : r < next r := by change r.val < (next r).val; simp [next_val, h]
  have hdist : ∀ c : Fin L,
      Nat.dist (snakeIndex (r, c)).val (snakeIndex (next r, c)).val +
        (snakeIndex (r, c)).val = (snakeIndex (next r, c)).val := by
    intro c
    have hc := (snake_index_row_lt hr c c).le
    rw [Nat.dist_eq_sub_of_le hc, Nat.sub_add_cancel hc]
  have hs := congrArg (fun f : Fin L → ℕ => ∑ c, f c) (funext hdist)
  simp only [Finset.sum_add_distrib, sum_snake_index_row, next_val, if_pos h] at hs
  change (∑ c : Fin L,
    Nat.dist (snakeIndex (r, c)).val (snakeIndex (next r, c)).val) = _
  nlinarith [hs]

/-- The last-to-first row transition retains the full periodic string length. -/
lemma sum_snake_vertical_row_of_last {L : ℕ} (hL : 2 ≤ L) (r : Fin L)
    (h : ¬r.val + 1 < L) :
    (∑ c : Fin L, Nat.dist (snakeIndex (r, c)).val (snakeIndex (down (r, c))).val) =
      L ^ 2 * (L - 1) := by
  have hr : r.val = L - 1 := by have := r.isLt; omega
  have hn : (next r).val = 0 := by simp [next_val, h]
  have hnr : next r < r := by change (next r).val < r.val; omega
  have hdist : ∀ c : Fin L,
      Nat.dist (snakeIndex (r, c)).val (snakeIndex (next r, c)).val +
        (snakeIndex (next r, c)).val = (snakeIndex (r, c)).val := by
    intro c
    have hc := (snake_index_row_lt hnr c c).le
    rw [Nat.dist_eq_sub_of_le_right hc, Nat.sub_add_cancel hc]
  have hs := congrArg (fun f : Fin L → ℕ => ∑ c, f c) (funext hdist)
  simp only [Finset.sum_add_distrib, sum_snake_index_row, hn, hr] at hs
  change (∑ c : Fin L,
    Nat.dist (snakeIndex (r, c)).val (snakeIndex (next r, c)).val) = _
  nlinarith [hs]

lemma sum_snake_vertical_distance {L : ℕ} (hL : 2 ≤ L) :
    (∑ p : Site L, Nat.dist (snakeIndex p).val (snakeIndex (down p)).val) =
      2 * L ^ 2 * (L - 1) := by
  cases L with
  | zero => omega
  | succ k =>
    rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    have hrow (r : Fin k) :
        (∑ c : Fin (k + 1), Nat.dist (snakeIndex (r.castSucc, c)).val
          (snakeIndex (down (r.castSucc, c))).val) = (k + 1) ^ 2 :=
      sum_snake_vertical_row_of_lt r.castSucc (Nat.succ_lt_succ r.isLt)
    simp_rw [hrow]
    rw [sum_snake_vertical_row_of_last hL (Fin.last k) (by simp)]
    simp
    ring

/-- All bond distances in one spin sector, including both periodic wraps. -/
lemma sum_snake_bond_distances {L : ℕ} (hL : 2 ≤ L) :
    (∑ p : Site L, (Nat.dist (snakeIndex p).val (snakeIndex (right p)).val +
      Nat.dist (snakeIndex p).val (snakeIndex (down p)).val)) =
      2 * L * (L - 1) * (L + 1) := by
  rw [Finset.sum_add_distrib, sum_snake_horizontal_distance, sum_snake_vertical_distance hL]
  ring

end SquareTorus
