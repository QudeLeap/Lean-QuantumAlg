/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Search.WalkCost
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Triangle predicates and candidate cost expressions

Graph predicates and scalar expressions supporting nested search [dW19, qcnotes.tex:3378-3421].
No program or asymptotic query bound is asserted.
-/

@[expose] public section

namespace QuantumAlg.TriangleSearch

open QuantumAlg

open Finset
open scoped BigOperators

/-- A graph `G` on `N` vertices contains a triangle:
three distinct vertices `u,v,w` pairwise adjacent in `G`. -/
def HasTriangle {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∃ (u v w : Fin N), u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
    G.Adj u v ∧ G.Adj v w ∧ G.Adj w u

/-- A triangle implies the graph has at least 3 vertices. -/
lemma HasTriangle.has_three_vertices {N : ℕ} {G : SimpleGraph (Fin N)}
    (h : HasTriangle G) : 3 ≤ N := by
  rcases h with ⟨u, v, w, h_uv, h_uw, h_vw, h_adj_uv, h_adj_vw, h_adj_wu⟩
  by_contra! hN
  -- hN: N < 3 → Fin N has at most 2 distinct elements
  -- But u ≠ v ≠ w are three distinct elements → contradiction
  have h_vals : Fintype.card (Fin N) = N := Fintype.card_fin N
  -- Since u,v,w are Finset elements with distinct val, the Finset {u,v,w} has card 3
  have h_finset_card : ({u, v, w} : Finset (Fin N)).card = 3 := by
    simp [h_uv, h_uw, h_vw]
  -- But any Finset of Fin N has card ≤ Fintype.card (Fin N) = N < 3
  have h_card_bound : ({u, v, w} : Finset (Fin N)).card ≤ Fintype.card (Fin N) :=
    Finset.card_le_univ ({u, v, w} : Finset (Fin N))
  rw [h_finset_card, h_vals] at h_card_bound
  omega

/-- The arithmetic number of unordered pairs among `r` objects. -/
def pairCount (r : ℕ) : ℕ := (r * (r - 1)) / 2

/-- The unordered-pair expression equals the binomial coefficient. -/
lemma pairCount_eq_choose_two (r : ℕ) : pairCount r = Nat.choose r 2 := by
  rw [pairCount, Nat.choose_two_right]

/-- An r-subset R contains a triangle edge if `∃ u ≠ v ∈ R, ∃ w, {u,v,w} triangle`. -/
def containsTriangleEdge {N : ℕ} (G : SimpleGraph (Fin N)) (R : Finset (Fin N)) : Prop :=
  ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ ∃ w : Fin N, w ≠ u ∧ w ≠ v ∧
    G.Adj u v ∧ G.Adj v w ∧ G.Adj w u

/-- A triangle supplies a finite subset containing one of its edges. -/
lemma HasTriangle.exists_marked_R {N : ℕ} {G : SimpleGraph (Fin N)} (h : HasTriangle G) :
    ∃ (R : Finset (Fin N)), containsTriangleEdge G R := by
  rcases h with ⟨u, v, w, h_uv, h_uw, h_vw, h_adj_uv, h_adj_vw, h_adj_wu⟩
  refine ⟨{u, v}, u, by simp, v, by simp, h_uv, w, h_uw.symm, h_vw.symm,
    h_adj_uv, h_adj_vw, h_adj_wu⟩

/-- The candidate setup expression for an `(r+1)`-element subset. -/
def outerSetupExpression (r : ℕ) : ℕ := pairCount (r + 1)

lemma outerSetupExpression_eq (r : ℕ) : outerSetupExpression r = Nat.choose (r + 1) 2 :=
  pairCount_eq_choose_two (r + 1)

/-- The candidate update expression `2*r-2`. -/
def outerUpdateExpression (r : ℕ) : ℕ := 2 * r - 2

/-- Update cost formula: U = 2(r-1) when r ≥ 1. -/
lemma outerUpdateExpression_eq (r : ℕ) (hr : 1 ≤ r) : outerUpdateExpression r = 2 * (r - 1) := by
  rw [outerUpdateExpression]
  omega

/-- An externally supplied check-cost parameter. -/
def outerCheckExpression (innerWalkCost : ℕ) : ℕ := innerWalkCost

/-- Nonnegativity of half a squared ratio of natural parameters. -/
lemma halfSquaredRatio_nonneg (N r : ℕ) (_hr_ge_2 : 2 ≤ r) (_hr_lt_N : r < N) :
    (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2) ≥ 0 := by
  positivity

/-- The reciprocal of a positive real is nonnegative. -/
lemma reciprocal_nonneg (r : ℝ) (hr_pos : 0 < r) : 1 / r ≥ 0 := by
  positivity


/-- An s-subset S of an r-set R contains a candidate triangle edge
if there exist distinct u, v ∈ S with a common neighbour in G. -/
def innerContainsTriangleEdge {N : ℕ} (G : SimpleGraph (Fin N)) (R S : Finset (Fin N)) : Prop :=
  ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ u ∈ S ∧ v ∈ S ∧
    ∃ w : Fin N, w ≠ u ∧ w ≠ v ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u

/-- The candidate inner setup expression. -/
def innerSetupExpression (s : ℕ) : ℕ := pairCount (s + 1)

/-- The candidate inner update expression. -/
def innerUpdateExpression (s : ℕ) : ℕ := 2 * s - 2

/-- The ceiling of a square root as a scalar cost parameter. -/
noncomputable def sqrtCeilExpression (N : ℕ) : ℕ := Nat.ceil (Real.sqrt (N : ℝ))

/-- The reciprocal of a positive real is positive. -/
lemma reciprocal_pos (s : ℝ) (hs_pos : 0 < s) : 0 < 1 / s := by
  positivity

/-- Nonnegativity of half a squared real ratio. -/
lemma halfSquaredRealRatio_nonneg (r s : ℝ) (hr_pos : 0 < r) (hs_pos : 0 < s)
    (_hs_le_r : s ≤ r) : (1/2 : ℝ) * ((s / r) ^ 2) ≥ 0 := by
  positivity

/-- Nonnegativity of the displayed scalar expression. -/
lemma innerCostExpression_nonneg (r s N : ℕ) :
    (innerSetupExpression s : ℝ) + (Real.pi / (4 * Real.sqrt ((s : ℝ) / (r : ℝ))) + 1) *
    ((sqrtCeilExpression N : ℝ) +
      (2 * Real.pi * Real.sqrt (s : ℝ)) * (innerUpdateExpression s : ℝ)) ≥ 0 := by
  positivity

/-- The rounded outer scalar cost expression, with externally supplied inner cost. -/
noncomputable def outerCostExpression (N r : ℕ) (C_inner : ℕ) : ℝ :=
  let ε := (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2)
  let δ := 1 / (r : ℝ)
  let η := (1/2 : ℝ)
  let t₁ := Nat.ceil (Real.pi / (4 * Real.sqrt ε))
  let t₂ := Nat.ceil (Real.logb 2 (Real.pi / Real.sqrt (2 * η * δ)))
  (walkCost (outerSetupExpression r) C_inner (outerUpdateExpression r) t₁ t₂ : ℝ)

/-- The rounded inner scalar cost expression. -/
noncomputable def innerRoundedCostExpression (N r s : ℕ) : ℝ :=
  let ε := (1/2 : ℝ) * (((s : ℝ) / (r : ℝ)) ^ 2)
  let δ := 1 / (s : ℝ)
  let η := (1/2 : ℝ)
  let t₁ := Nat.ceil (Real.pi / (4 * Real.sqrt ε))
  let t₂ := Nat.ceil (Real.logb 2 (Real.pi / Real.sqrt (2 * η * δ)))
  (walkCost (innerSetupExpression s) (sqrtCeilExpression N) (innerUpdateExpression s) t₁ t₂ : ℝ)

/-- Nonnegativity of the nested scalar cost expression. -/
lemma nestedCostExpression_nonneg (N r s : ℕ) :
    outerCostExpression N r (Nat.ceil (innerRoundedCostExpression N r s)) ≥ 0 := by
  unfold outerCostExpression walkCost
  push_cast
  positivity

end QuantumAlg.TriangleSearch
