/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Expansion
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation

/-!
# Width-only resource bounds for actual known-order preparation

The binary gaps telescope before any order is specialized. These bounds apply
to every positive order, including one and powers of two, without evaluating
its list of set-bit positions at a fixed cryptographic size. The exact native
counts remain those of the actual Shukla--Vedula preparation word.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation

noncomputable section

open scoped BigOperators

variable {N : Nat}

/-- The set-bit position at an index, clamped to the highest set bit. -/
private def clampedEll (expansion : OrderExpansion N) (index : Nat) : Nat :=
  expansion.ell ⟨min index expansion.gaps, by
    have positive := expansion.count_pos
    have bounded : min index (expansion.count - 1) ≤ expansion.count - 1 :=
      Nat.min_le_right _ _
    change min index (expansion.count - 1) < expansion.count
    omega⟩

private lemma clampedEll_monotone (expansion : OrderExpansion N) :
    Monotone (clampedEll expansion) := by
  intro left right hleft
  apply expansion.ell_strict.monotone
  change min left expansion.gaps ≤ min right expansion.gaps
  exact min_le_min hleft le_rfl

private lemma clampedEll_zero (expansion : OrderExpansion N) :
    clampedEll expansion 0 = expansion.first := by
  simp [clampedEll, OrderExpansion.first]

private lemma clampedEll_last (expansion : OrderExpansion N) :
    clampedEll expansion expansion.gaps = expansion.last := by
  simp [clampedEll, OrderExpansion.last, OrderExpansion.gaps]

/-- The real gaps of an arbitrary order telescope to the span of its set bits. -/
public lemma orderPreparation_gapWidths_sum (expansion : OrderExpansion N) :
    ∑ gap : Fin expansion.gaps, gapWidth expansion gap =
      expansion.last - expansion.first := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ index ∈ Finset.range expansion.gaps,
        (clampedEll expansion (index + 1) - clampedEll expansion index) := by
      apply Finset.sum_congr rfl
      intro index member
      have bounded : index < expansion.gaps := Finset.mem_range.mp member
      simp only [dif_pos bounded]
      change gapWidth expansion ⟨index, bounded⟩ = _
      simp [gapWidth, leftIndex, rightIndex, clampedEll,
        Nat.min_eq_left (Nat.le_of_lt bounded),
        Nat.min_eq_left (Nat.succ_le_iff.mpr bounded)]
    _ = clampedEll expansion expansion.gaps - clampedEll expansion 0 :=
      Finset.sum_range_tsub (clampedEll_monotone expansion) expansion.gaps
    _ = expansion.last - expansion.first := by
      rw [clampedEll_last, clampedEll_zero]

/-- Strict binary gaps use at least one bit position each. -/
public lemma orderPreparation_gaps_le_span (expansion : OrderExpansion N) :
    expansion.gaps ≤ expansion.last - expansion.first := by
  rw [← orderPreparation_gapWidths_sum expansion]
  calc
    expansion.gaps = ∑ _gap : Fin expansion.gaps, 1 := by simp
    _ ≤ ∑ gap : Fin expansion.gaps, gapWidth expansion gap := by
      apply Finset.sum_le_sum
      intro gap _
      unfold gapWidth
      have strict := ell_left_lt_right expansion gap
      omega

private lemma first_le_last (expansion : OrderExpansion N) :
    expansion.first ≤ expansion.last := by
  unfold OrderExpansion.first OrderExpansion.last
  apply expansion.ell_strict.monotone
  change 0 ≤ expansion.count - 1
  omega

private lemma oneQubitControls_le (expansion : OrderExpansion N) :
    (∑ gap : Fin expansion.gaps, if gap.val = 0 then 1 else 4) ≤
      4 * expansion.gaps := by
  calc
    _ ≤ ∑ _gap : Fin expansion.gaps, 4 := by
      apply Finset.sum_le_sum
      intro gap _
      split <;> omega
    _ = 4 * expansion.gaps := by simp [mul_comm]

private lemma cnotControls_le (expansion : OrderExpansion N) :
    (∑ gap : Fin expansion.gaps, if gap.val = 0 then 0 else 2) ≤
      2 * expansion.gaps := by
  calc
    _ ≤ ∑ _gap : Fin expansion.gaps, 2 := by
      apply Finset.sum_le_sum
      intro gap _
      split <;> omega
    _ = 2 * expansion.gaps := by simp [mul_comm]

private lemma depthControls_le (expansion : OrderExpansion N) :
    (∑ gap : Fin expansion.gaps, if gap.val = 0 then 1 else 5) ≤
      5 * expansion.gaps := by
  calc
    _ ≤ ∑ _gap : Fin expansion.gaps, 5 := by
      apply Finset.sum_le_sum
      intro gap _
      split <;> omega
    _ = 5 * expansion.gaps := by simp [mul_comm]

/-- Actual native one-qubit count is bounded before specializing the order. -/
public lemma orderPreparation_singleQubitCount_le (expansion : OrderExpansion N) :
    singleQubitCount expansion ≤ expansion.singleQubitBound := by
  have controls := oneQubitControls_le expansion
  have span := orderPreparation_gapWidths_sum expansion
  have ordered := first_le_last expansion
  unfold singleQubitCount OrderExpansion.singleQubitBound
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  omega

/-- Actual native CNOT count is bounded before specializing the order. -/
public lemma orderPreparation_cnotCount_le (expansion : OrderExpansion N) :
    cnotCount expansion ≤ expansion.cnotBound := by
  have controls := cnotControls_le expansion
  have span := orderPreparation_gapWidths_sum expansion
  unfold cnotCount OrderExpansion.cnotBound
  simp only [Finset.sum_add_distrib]
  omega

/-- Actual preparation depth retains its complete sequential gap dependence. -/
public lemma orderPreparation_unitDepth_le (expansion : OrderExpansion N) :
    unitDepth expansion ≤ expansion.depthBound := by
  have controls := depthControls_le expansion
  have span := orderPreparation_gapWidths_sum expansion
  have gaps := orderPreparation_gaps_le_span expansion
  unfold unitDepth OrderExpansion.depthBound
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  split <;> omega

/-- A width certificate bounds all set-bit gaps without expanding them. -/
public lemma orderPreparation_scalarBounds_of_last_lt
    (expansion : OrderExpansion N) (width : Nat) (last_lt : expansion.last < width) :
    singleQubitCount expansion ≤ 11 * width ∧
      cnotCount expansion ≤ 3 * width ∧
      unitDepth expansion ≤ 10 * width + 1 := by
  have first := first_le_last expansion
  have gaps := orderPreparation_gaps_le_span expansion
  have one := orderPreparation_singleQubitCount_le expansion
  have cnot := orderPreparation_cnotCount_le expansion
  have depth := orderPreparation_unitDepth_le expansion
  unfold OrderExpansion.singleQubitBound at one
  unfold OrderExpansion.cnotBound at cnot
  unfold OrderExpansion.depthBound at depth
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Actual preparation costs depend only on the symbolic reviewed register width. -/
public lemma orderPreparation_scalarBounds
    {G : Type*} [Group G] (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    singleQubitCount expansion ≤ 11 * width P ∧
      cnotCount expansion ≤ 3 * width P ∧
      unitDepth expansion ≤ 10 * width P + 1 := by
  have last_lt : expansion.last < width P := by
    exact ell_lt_width P expansion ⟨expansion.count - 1, by
      have := expansion.count_pos
      omega⟩
  exact orderPreparation_scalarBounds_of_last_lt expansion (width P) last_lt

end

end QuantumAlg.FiniteCyclicDLP.OrderPreparation
