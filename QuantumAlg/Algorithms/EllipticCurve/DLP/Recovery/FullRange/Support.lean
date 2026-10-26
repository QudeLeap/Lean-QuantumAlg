/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# Full power-of-two exponent support

Both exponent registers are uniform on their entire physical basis.  The
exceptional mass below is the sum of their actual squared amplitudes on the
branch-dependent schedule's bad set.  No subgroup-order truncation or
renormalization enters this definition.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open scoped BigOperators

/-- Two complete exponent registers, with no subgroup-order cutoff. -/
abbrev Branch (width : Nat) := Fin (2 ^ width) × Fin (2 ^ width)

/-- A certified uniform state on every physical exponent label. -/
def exponentState (width : Nat) : NormalizedVector (Qubits width) :=
  FiniteCyclicDLP.rangeUniformState (2 ^ width) width (Nat.two_pow_pos width) (le_refl _)

/-- Every physical exponent label has the same amplitude. -/
lemma exponentState_apply (width : Nat) (index : Fin (2 ^ width)) :
    exponentState width index = FiniteCyclicDLP.invSqrtOrder (2 ^ width) := by
  simp only [exponentState, FiniteCyclicDLP.rangeUniformState_apply, if_pos index.isLt]

/-- The product amplitude of the two full-range exponent states. -/
def branchAmplitude (width : Nat) (branch : Branch width) : ℂ :=
  exponentState width branch.1 * exponentState width branch.2

/-- Full-range squared amplitudes use the physical cardinality, independently
of the group order and of all branch-dependent window addends. -/
lemma branchAmplitude_norm_sq (width : Nat) (branch : Branch width) :
    ‖branchAmplitude width branch‖ ^ 2 =
      ((2 ^ width : Nat) : ℝ)⁻¹ * ((2 ^ width : Nat) : ℝ)⁻¹ := by
  simp only [branchAmplitude, exponentState_apply, norm_mul, mul_pow,
    FiniteCyclicDLP.norm_sq_invSqrtOrder (Nat.two_pow_pos width)]

/-- The complete pair of registers has exactly the physical square cardinality. -/
lemma branch_card (width : Nat) : Fintype.card (Branch width) = 2 ^ width * 2 ^ width := by
  simp only [Branch, Fintype.card_prod, Fintype.card_fin]

variable {G : Type*} [Group G]

/-- Full-range branches on which every selected group addition is admissible. -/
def admissibleBranches (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) : Finset (Branch width) := by
  classical
  exact Finset.univ.filter fun branch =>
    ExceptionalOffsetAveraging.Admissible steps selected (addend branch) seed branch

/-- Bad branches for one fixed seed and a possibly address-dependent schedule. -/
def exceptionalBranches (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) : Finset (Branch width) := by
  classical
  exact Finset.univ.filter fun branch =>
    ¬ ExceptionalOffsetAveraging.Admissible steps selected (addend branch) seed branch

/-- The unnormalized admissible and exceptional components partition all
physical exponent labels, including those beyond the subgroup order. -/
lemma branches_partition (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) :
    admissibleBranches width steps selected addend seed ∪
      exceptionalBranches width steps selected addend seed = Finset.univ := by
  classical
  ext branch
  simp only [admissibleBranches, exceptionalBranches, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  tauto

lemma branches_disjoint (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) :
    Disjoint (admissibleBranches width steps selected addend seed)
      (exceptionalBranches width steps selected addend seed) := by
  classical
  rw [Finset.disjoint_left]
  intro branch good bad
  exact (Finset.mem_filter.mp bad).2 (Finset.mem_filter.mp good).2

/-- Squared-amplitude mass of precisely the bad full-range branches. -/
def exceptionalMass (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) : ℝ :=
  ∑ branch ∈ exceptionalBranches width steps selected addend seed,
    ‖branchAmplitude width branch‖ ^ 2

/-- Counting bad full-range branches gives their exact Born mass. -/
lemma exceptionalMass_eq_card_div (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) :
    exceptionalMass width steps selected addend seed =
      (exceptionalBranches width steps selected addend seed).card /
        (((2 ^ width : Nat) : ℝ) * ((2 ^ width : Nat) : ℝ)) := by
  unfold exceptionalMass
  simp_rw [branchAmplitude_norm_sq]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The two-register squared amplitudes sum to one over the full physical
support, including labels at least the subgroup order. -/
lemma branchAmplitude_square_sum (width : Nat) :
    ∑ branch : Branch width, ‖branchAmplitude width branch‖ ^ 2 = 1 := by
  simp_rw [branchAmplitude_norm_sq]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, branch_card]
  norm_num only [Nat.cast_mul]
  have positive : (0 : ℝ) < ((2 ^ width : Nat) : ℝ) := by positivity
  field_simp

/-- Cross-multiplied finite averaging bounds the actual full-range mass. -/
lemma exceptionalMass_le_of_card_bound (width steps denominator budget : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G)
    (denominatorPositive : 0 < denominator)
    (bound : denominator * (exceptionalBranches width steps selected addend seed).card ≤
      (2 ^ width * 2 ^ width) * budget) :
    exceptionalMass width steps selected addend seed ≤ (budget : ℝ) / denominator := by
  rw [exceptionalMass_eq_card_div]
  have physicalPositive : (0 : ℝ) < ((2 ^ width : Nat) : ℝ) := by positivity
  have denominatorPositiveReal : (0 : ℝ) < denominator := by exact_mod_cast denominatorPositive
  apply (div_le_div_iff₀ (mul_pos physicalPositive physicalPositive)
    denominatorPositiveReal).2
  have boundReal : ((denominator *
      (exceptionalBranches width steps selected addend seed).card : Nat) : ℝ) ≤
      (((2 ^ width * 2 ^ width) * budget : Nat) : ℝ) := by exact_mod_cast bound
  simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using boundReal

end

end QuantumAlg.EllipticCurve.FullRange
