/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Arithmetic
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Arithmetic

/-!
# Residual blocks for nontrivial known-order preparation

The Shukla--Vedula induction partitions the represented range into aligned
power-of-two blocks. This module defines those raw vectors and proves that
their certified weighted sum is pointwise the desired uniform range vector.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

open scoped BigOperators

variable {N : Nat}

/-- The normalized aligned block at one set-bit position, represented in any
ambient binary width. -/
public def residualBlockAt (expansion : PositiveGapExpansion N)
    (registerWidth : Nat) (source : Fin (expansion.gaps + 1)) :
    HilbertVector (Qubits registerWidth) :=
  WithLp.toLp 2 fun address =>
    if expansion.residualSupport source address.val then
      OrderPreparation.invSqrtOrder (2 ^ expansion.ell source)
    else 0

/-- The aligned block at the expansion's intrinsic highest-bit width. -/
public def residualBlock (expansion : PositiveGapExpansion N)
    (source : Fin (expansion.gaps + 1)) :
    HilbertVector (Qubits expansion.width) :=
  expansion.residualBlockAt expansion.width source

/-- Pointwise form of an aligned residual block. -/
@[simp] public lemma residualBlock_apply (expansion : PositiveGapExpansion N)
    (source : Fin (expansion.gaps + 1))
    (address : Fin (2 ^ expansion.width)) :
    expansion.residualBlock source address =
      if expansion.residualSupport source address.val then
        OrderPreparation.invSqrtOrder (2 ^ expansion.ell source)
      else 0 := by
  rfl

/-- Pointwise form of an aligned block in an arbitrary ambient width. -/
@[simp] public lemma residualBlockAt_apply (expansion : PositiveGapExpansion N)
    (registerWidth : Nat) (source : Fin (expansion.gaps + 1))
    (address : Fin (2 ^ registerWidth)) :
    expansion.residualBlockAt registerWidth source address =
      if expansion.residualSupport source address.val then
        OrderPreparation.invSqrtOrder (2 ^ expansion.ell source)
      else 0 := by
  rfl

/-- An address outside a residual interval has zero block amplitude. -/
public lemma residualBlock_apply_of_not_support
    (expansion : PositiveGapExpansion N)
    (source : Fin (expansion.gaps + 1))
    (address : Fin (2 ^ expansion.width))
    (outside : ¬ expansion.residualSupport source address.val) :
    expansion.residualBlock source address = 0 := by
  rw [residualBlock_apply, if_neg outside]

/-- An address outside a residual interval has zero amplitude at every
ambient width. -/
public lemma residualBlockAt_apply_of_not_support
    (expansion : PositiveGapExpansion N) (registerWidth : Nat)
    (source : Fin (expansion.gaps + 1))
    (address : Fin (2 ^ registerWidth))
    (outside : ¬ expansion.residualSupport source address.val) :
    expansion.residualBlockAt registerWidth source address = 0 := by
  rw [residualBlockAt_apply, if_neg outside]

/-- The represented uniform-range vector at an arbitrary ambient width. -/
public def rangeVectorAt (_expansion : PositiveGapExpansion N)
    (registerWidth : Nat) : HilbertVector (Qubits registerWidth) :=
  WithLp.toLp 2 fun address =>
    if address.val < N then OrderPreparation.invSqrtOrder N else 0

/-- The represented uniform-range vector at the intrinsic expansion width. -/
public def rangeVector (expansion : PositiveGapExpansion N) :
    HilbertVector (Qubits expansion.width) :=
  expansion.rangeVectorAt expansion.width

/-- Pointwise form of the intrinsic uniform-range vector. -/
@[simp] public lemma rangeVector_apply (expansion : PositiveGapExpansion N)
    (address : Fin (2 ^ expansion.width)) :
    expansion.rangeVector address =
      if address.val < N then OrderPreparation.invSqrtOrder N else 0 := by
  rfl

@[simp] public lemma rangeVectorAt_apply (expansion : PositiveGapExpansion N)
    (registerWidth : Nat) (address : Fin (2 ^ registerWidth)) :
    expansion.rangeVectorAt registerWidth address =
      if address.val < N then OrderPreparation.invSqrtOrder N else 0 := by
  rfl

/-- A natural prefix length names its clamped source position. -/
private def sourcePosition (expansion : PositiveGapExpansion N) (count : Nat) :
    Fin (expansion.gaps + 1) :=
  ⟨min count expansion.gaps, by omega⟩

private lemma sourcePosition_eq_of_le (expansion : PositiveGapExpansion N)
    {count : Nat} (bounded : count ≤ expansion.gaps) :
    expansion.sourcePosition count = ⟨count, by omega⟩ := by
  apply Fin.ext
  simp [sourcePosition, Nat.min_eq_left bounded]

/-- The aligned source intervals cover every address below the represented
order. -/
public lemma residualSupport_exists_of_lt_order
    (expansion : PositiveGapExpansion N) {address : Nat}
    (below : address < N) :
    ∃ source : Fin (expansion.gaps + 1),
      expansion.residualSupport source address := by
  classical
  let predicate : Nat → Prop := fun count =>
    count ≤ expansion.gaps ∧
      expansion.tailMass (expansion.sourcePosition count) ≤ address
  have existsPosition : ∃ count, predicate count := by
    refine ⟨expansion.gaps, Nat.le_refl _, ?_⟩
    have lastPosition : expansion.sourcePosition expansion.gaps =
        Fin.last expansion.gaps := by
      apply Fin.ext
      simp [sourcePosition]
    rw [lastPosition, expansion.tailMass_last]
    exact Nat.zero_le address
  let count := Nat.find existsPosition
  have specification : predicate count := by
    simpa [count] using Nat.find_spec existsPosition
  have bounded : count ≤ expansion.gaps := specification.1
  refine ⟨expansion.sourcePosition count, specification.2, ?_⟩
  by_cases first : count = 0
  · rw [first]
    have positionZero : expansion.sourcePosition 0 =
        (0 : Fin (expansion.gaps + 1)) :=
      expansion.sourcePosition_eq_of_le (by omega)
    rw [positionZero]
    have partition := expansion.prefixMass_add_current_add_tailMass
      (⟨0, expansion.gaps_pos⟩ : Fin expansion.gaps)
    rw [expansion.prefixMass_zero] at partition
    have top : expansion.tailMass (0 : Fin (expansion.gaps + 1)) +
        2 ^ expansion.ell (0 : Fin (expansion.gaps + 1)) = N := by
      simpa [Nat.add_comm] using partition
    omega
  · have countPositive : 0 < count := Nat.pos_of_ne_zero first
    have previousBound : count - 1 ≤ expansion.gaps := by omega
    have notPrevious : ¬ predicate (count - 1) := by
      intro previous
      have least : count ≤ count - 1 := by
        dsimp [count]
        exact Nat.find_min' existsPosition previous
      omega
    have previousBase :
        address < expansion.tailMass (expansion.sourcePosition (count - 1)) := by
      have notBelow :
          ¬ expansion.tailMass (expansion.sourcePosition (count - 1)) ≤ address := by
        intro atMost
        exact notPrevious ⟨previousBound, atMost⟩
      omega
    let gap : Fin expansion.gaps := ⟨count - 1, by omega⟩
    have previousPosition : expansion.sourcePosition (count - 1) =
        gap.castSucc := by
      apply Fin.ext
      simp [sourcePosition, gap, Nat.min_eq_left previousBound]
    have currentPosition : expansion.sourcePosition count = gap.succ := by
      apply Fin.ext
      change min count expansion.gaps = count - 1 + 1
      rw [Nat.min_eq_left bounded]
      omega
    have adjacent := expansion.tailMass_eq_pow_add_tailMass_succ gap
    rw [currentPosition]
    rw [previousPosition] at previousBase
    omega

/-- An address belongs to at most one aligned source interval. -/
public lemma residualSupport_unique (expansion : PositiveGapExpansion N)
    {left right : Fin (expansion.gaps + 1)} {address : Nat}
    (leftSupport : expansion.residualSupport left address)
    (rightSupport : expansion.residualSupport right address) :
    left = right := by
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · exact expansion.residualSupport_disjoint_of_lt before address
      ⟨leftSupport, rightSupport⟩
  · exact expansion.residualSupport_disjoint_of_lt after address
      ⟨rightSupport, leftSupport⟩

/-- A block weight times its normalized block amplitude is the common target
amplitude. -/
public lemma blockWeight_mul_residualAmplitude
    (expansion : PositiveGapExpansion N)
    (source : Fin (expansion.gaps + 1)) :
    (expansion.blockWeight source : Complex) *
        OrderPreparation.invSqrtOrder (2 ^ expansion.ell source) =
      OrderPreparation.invSqrtOrder N := by
  have powerPositive : 0 < ((2 ^ expansion.ell source : Nat) : Real) := by
    positivity
  have orderPositive : 0 < (N : Real) := by
    exact_mod_cast expansion.positive
  have powerSqrt :
      (Real.sqrt ((2 ^ expansion.ell source : Nat) : Real) : Complex) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr powerPositive)
  have orderSqrt : (Real.sqrt (N : Real) : Complex) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr orderPositive)
  unfold blockWeight OrderPreparation.invSqrtOrder
  rw [Real.sqrt_div (Nat.cast_nonneg _), Complex.ofReal_div]
  field_simp [powerSqrt, orderSqrt]

/-- The weighted aligned blocks are pointwise the uniform vector over the
represented range. -/
public lemma blockSum_eq_rangeVector (expansion : PositiveGapExpansion N) :
    (∑ source : Fin (expansion.gaps + 1),
      (expansion.blockWeight source : Complex) •
        expansion.residualBlock source) =
      expansion.rangeVector := by
  apply WithLp.ofLp_injective
  funext address
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [rangeVector_apply]
  by_cases below : address.val < N
  · obtain ⟨source, support⟩ :=
      expansion.residualSupport_exists_of_lt_order below
    rw [Finset.sum_eq_single source]
    · rw [residualBlock_apply, if_pos support,
        expansion.blockWeight_mul_residualAmplitude source, if_pos below]
    · intro other _ different
      have outside : ¬ expansion.residualSupport other address.val := by
        intro otherSupport
        have same := expansion.residualSupport_unique otherSupport support
        exact different same
      rw [expansion.residualBlock_apply_of_not_support other address outside]
      simp
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [below]
    · intro source _
      have outside : ¬ expansion.residualSupport source address.val := by
        intro support
        have bound := expansion.tailMass_add_current_le source
        exact below (lt_of_lt_of_le support.2 bound)
      rw [expansion.residualBlock_apply_of_not_support source address outside]
      simp

/-- The same weighted block partition is valid in every ambient binary
register that contains the represented range. -/
public lemma blockSumAt_eq_rangeVectorAt (expansion : PositiveGapExpansion N)
    (registerWidth : Nat) (_fits : N ≤ 2 ^ registerWidth) :
    (∑ source : Fin (expansion.gaps + 1),
      (expansion.blockWeight source : Complex) •
        expansion.residualBlockAt registerWidth source) =
      expansion.rangeVectorAt registerWidth := by
  apply WithLp.ofLp_injective
  funext address
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [rangeVectorAt_apply]
  by_cases below : address.val < N
  · obtain ⟨source, support⟩ :=
      expansion.residualSupport_exists_of_lt_order below
    rw [Finset.sum_eq_single source]
    · rw [residualBlockAt_apply, if_pos support,
        expansion.blockWeight_mul_residualAmplitude source, if_pos below]
    · intro other _ different
      have outside : ¬ expansion.residualSupport other address.val := by
        intro otherSupport
        have same := expansion.residualSupport_unique otherSupport support
        exact different same
      rw [expansion.residualBlockAt_apply_of_not_support registerWidth
        other address outside]
      simp
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [below]
    · intro source _
      have outside : ¬ expansion.residualSupport source address.val := by
        intro support
        have bound := expansion.tailMass_add_current_le source
        exact below (lt_of_lt_of_le support.2 bound)
      rw [expansion.residualBlockAt_apply_of_not_support registerWidth
        source address outside]
      simp

end


end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
