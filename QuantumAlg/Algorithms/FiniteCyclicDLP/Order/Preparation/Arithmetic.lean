/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Expansion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Order.Monotone.Defs

/-!
# Arithmetic for nontrivial known-order range preparation

This module proves the binary-mass partition, rotation coefficients, and gap
telescoping identities used by the native Shukla--Vedula preparation.  Its
input is the positive-gap view derived from the canonical order expansion.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

open scoped BigOperators

variable {N : Nat}

/-- The binary mass strictly above source position `m`.  This is the aligned
base address of the `m`th normalized residual block: all of its lower
`ell m` bits are free, while the set bits above `ell m` remain fixed. -/
public def tailMass (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1)) : Nat :=
  ∑ j : Fin (b.gaps + 1),
    if m.val < j.val then 2 ^ b.ell j else 0
/-- Pointwise support predicate for one aligned residual block. -/
@[expose] public def residualSupport (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1))
    (index : Nat) : Prop :=
  b.tailMass m ≤ index ∧ index < b.tailMass m + 2 ^ b.ell m

/-- Membership in an aligned residual block is decidable from its two natural
number bounds.  Keeping this instance with the predicate makes the public
pointwise block formulas elaborate without importing classical choice. -/
public instance residualSupportDecidable (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) (index : Nat) :
    Decidable (b.residualSupport m index) := by
  unfold residualSupport
  infer_instance
/-- The binary mass strictly below an arbitrary source position.  Unlike the
stage-indexed `prefixMass`, this includes the terminal position and is the
natural index for the residual-block induction. -/
public def lowerMass (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1)) : Nat :=
  ∑ j : Fin (b.gaps + 1),
    if j.val < m.val then 2 ^ b.ell j else 0

@[simp]
public theorem lowerMass_zero (b : PositiveGapExpansion N) : b.lowerMass 0 = 0 := by
  unfold lowerMass
  simp

/-- Passing one source bit adds exactly that bit's binary mass to the lower
prefix. -/
public theorem lowerMass_succ (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    b.lowerMass m.succ = b.lowerMass m.castSucc + 2 ^ b.ell m.castSucc := by
  calc
    b.lowerMass m.succ = ∑ index : Fin (b.gaps + 1),
        ((if index.val < m.castSucc.val then 2 ^ b.ell index else 0) +
          if index = m.castSucc then 2 ^ b.ell index else 0) := by
          unfold lowerMass
          apply Finset.sum_congr rfl
          intro index _
          by_cases hcurrent : index = m.castSucc
          · subst index
            have hbelow : ¬ m.castSucc.val < m.castSucc.val := Nat.lt_irrefl _
            have hsucc : m.val < m.val + 1 := Nat.lt_succ_self m.val
            simp only [Fin.val_castSucc, Fin.val_succ, lt_self_iff_false,
              if_false, if_true, zero_add, hsucc]
          by_cases hbelow : index.val < m.castSucc.val
          · have hbelow' : index.val < m.val := by
              simpa only [Fin.val_castSucc] using hbelow
            have hle : index.val ≤ m.val := Nat.le_of_lt hbelow'
            have hsucc : index.val < m.succ.val := by
              simpa only [Fin.val_succ, Nat.lt_add_one_iff] using hle
            simp only [Fin.val_castSucc, hbelow', if_true, hcurrent,
              if_false, add_zero, hsucc]
          · have hneVal : index.val ≠ m.val := by
              intro hval
              apply hcurrent
              apply Fin.ext
              simpa only [Fin.val_castSucc] using hval
            have hbelow' : ¬ index.val < m.val := by
              simpa only [Fin.val_castSucc] using hbelow
            have hnotle : ¬ index.val ≤ m.val := by omega
            have hsucc : ¬ index.val < m.succ.val := by
              simpa only [Fin.val_succ, Nat.lt_add_one_iff] using hnotle
            simp only [Fin.val_castSucc, hbelow', if_false, hcurrent,
              zero_add, hsucc]
    _ = (∑ index : Fin (b.gaps + 1),
        if index.val < m.castSucc.val then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.gaps + 1),
            if index = m.castSucc then 2 ^ b.ell index else 0 := by
          rw [Finset.sum_add_distrib]
    _ = b.lowerMass m.castSucc + 2 ^ b.ell m.castSucc := by
          simp [lowerMass]

/-- The partial binary mass strictly below the source position `m`. -/
@[expose] public def prefixMass (b : PositiveGapExpansion N) (m : Fin b.gaps) : Nat :=
  ∑ j : Fin (b.gaps + 1),
    if j.val < m.val then 2 ^ b.ell j else 0

@[simp]
public theorem lowerMass_castSucc (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    b.lowerMass m.castSucc = b.prefixMass m := by
  rfl

/-- Consecutive aligned bases differ by exactly the next binary summand.
Thus the source blocks are adjacent intervals, in decreasing source-index
order. -/
public theorem tailMass_eq_pow_add_tailMass_succ (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    b.tailMass m.castSucc = 2 ^ b.ell m.succ + b.tailMass m.succ := by
  calc
    b.tailMass m.castSucc = ∑ index : Fin (b.gaps + 1),
        ((if index = m.succ then 2 ^ b.ell index else 0) +
          if m.succ.val < index.val then 2 ^ b.ell index else 0) := by
          unfold tailMass
          apply Finset.sum_congr rfl
          intro index _
          by_cases hnext : index = m.succ
          · subst index
            have hleft : m.val < m.val + 1 := Nat.lt_succ_self m.val
            simp only [Fin.val_castSucc, Fin.val_succ, if_true,
              lt_self_iff_false, if_false, add_zero, hleft]
          by_cases htail : m.succ.val < index.val
          · have htail' : m.val + 1 < index.val := by
              simpa only [Fin.val_succ] using htail
            have hleft : m.castSucc.val < index.val := by
              simpa only [Fin.val_castSucc] using (lt_trans (Nat.lt_succ_self _) htail')
            have hleft' : m.val < index.val := by
              simpa only [Fin.val_castSucc] using hleft
            simp only [Fin.val_castSucc, Fin.val_succ, hnext, if_false,
              hleft', htail', if_true, zero_add]
          · have hleft : ¬ m.castSucc.val < index.val := by
              have htail' : ¬ m.val + 1 < index.val := by
                simpa only [Fin.val_succ] using htail
              have hnextVal : index.val ≠ m.val + 1 := by
                intro hval
                apply hnext
                apply Fin.ext
                simpa only [Fin.val_succ] using hval
              simp only [Fin.val_castSucc]
              omega
            have hleft' : ¬ m.val < index.val := by
              simpa only [Fin.val_castSucc] using hleft
            have htail' : ¬ m.val + 1 < index.val := by
              simpa only [Fin.val_succ] using htail
            simp only [Fin.val_castSucc, Fin.val_succ, hnext, if_false,
              hleft', htail', zero_add]
    _ = (∑ index : Fin (b.gaps + 1),
        if index = m.succ then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.gaps + 1),
            if m.succ.val < index.val then 2 ^ b.ell index else 0 := by
          rw [Finset.sum_add_distrib]
    _ = 2 ^ b.ell m.succ + b.tailMass m.succ := by
          simp [tailMass]

@[simp]
public theorem tailMass_last (b : PositiveGapExpansion N) :
    b.tailMass (Fin.last b.gaps) = 0 := by
  unfold tailMass
  apply Finset.sum_eq_zero
  intro index _
  have hnot : ¬ (Fin.last b.gaps).val < index.val := by
    have hle : index.val ≤ b.gaps := Nat.le_of_lt_succ index.isLt
    simpa only [Fin.val_last, not_lt] using hle
  rw [if_neg hnot]

/-- A residual base together with its own binary summand is bounded by the
whole certified expansion.  This also supplies the range proof for the
literal high-register ket used in the tensor form of a residual block. -/
public theorem tailMass_add_current_le (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) :
    b.tailMass m + 2 ^ b.ell m ≤ N := by
  have hcurrent :
      2 ^ b.ell m = ∑ index : Fin (b.gaps + 1),
        if index = m then 2 ^ b.ell index else 0 := by
    simp
  rw [hcurrent]
  unfold tailMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ index : Fin (b.gaps + 1),
        ((if m.val < index.val then 2 ^ b.ell index else 0) +
          if index = m then 2 ^ b.ell index else 0) ≤
        ∑ index : Fin (b.gaps + 1), 2 ^ b.ell index := by
      apply Finset.sum_le_sum
      intro index _
      by_cases htail : m.val < index.val
      · have hne : index ≠ m := by
          intro heq
          subst index
          exact (Nat.lt_irrefl m.val) htail
        simp [htail, hne]
      · by_cases hcurrent : index = m
        · subst index
          simp
        · simp [htail, hcurrent]
    _ = N := b.sum_powers.symm

/-- Every residual base lies strictly below the represented positive order. -/
public theorem tailMass_lt_order (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) : b.tailMass m < N := by
  have hbound := b.tailMass_add_current_le m
  have hpositive : 0 < 2 ^ b.ell m := Nat.two_pow_pos _
  omega

/-- Every residual base fits inside the intrinsic highest-bit width. -/
public theorem tailMass_lt_pow_width (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) : b.tailMass m < 2 ^ b.width :=
  (b.tailMass_lt_order m).trans_le b.fits_proof

/-- Every summand strictly above `ell m` has the trailing zero bits needed to
make the residual block aligned at its own source position. -/
public theorem pow_succ_ell_dvd_tailMass (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) :
    2 ^ (b.ell m + 1) ∣ b.tailMass m := by
  unfold tailMass
  apply Finset.dvd_sum
  intro index _
  split_ifs with habove
  · apply pow_dvd_pow
    have hstrict : b.ell m < b.ell index :=
      b.ell_strict (by simpa using habove)
    omega
  · exact dvd_zero _
/-- The mass below a source position, its own summand, and the mass above it
form the certified binary expansion.  This is the arithmetic partition used
by the residual-block invariant. -/
public theorem prefixMass_add_current_add_tailMass (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    b.prefixMass m + 2 ^ b.ell m.castSucc + b.tailMass m.castSucc = N := by
  calc
    b.prefixMass m + 2 ^ b.ell m.castSucc + b.tailMass m.castSucc =
        (∑ index : Fin (b.gaps + 1),
          if index.val < m.val then 2 ^ b.ell index else 0) +
          (∑ index : Fin (b.gaps + 1),
            if index = m.castSucc then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.gaps + 1),
            if m.castSucc.val < index.val then 2 ^ b.ell index else 0 := by
          simp [prefixMass, tailMass]
    _ = ∑ index : Fin (b.gaps + 1),
        ((if index.val < m.val then 2 ^ b.ell index else 0) +
          (if index = m.castSucc then 2 ^ b.ell index else 0) +
          (if m.castSucc.val < index.val then 2 ^ b.ell index else 0)) := by
          simp_rw [Finset.sum_add_distrib]
    _ = ∑ index : Fin (b.gaps + 1), 2 ^ b.ell index := by
          apply Finset.sum_congr rfl
          intro index _
          rcases lt_trichotomy index.val m.val with hbelow | hcurrent | habove
          · have hne : index ≠ m.castSucc := by
              intro heq
              subst index
              simp at hbelow
            have htail : ¬ m.castSucc.val < index.val := by
              simp only [Fin.val_castSucc]
              omega
            simp only [hbelow, if_true, hne, if_false, htail, add_zero]
          · have heq : index = m.castSucc := Fin.ext (by simpa using hcurrent)
            subst index
            simp only [Fin.val_castSucc, lt_self_iff_false, if_false,
              if_true, zero_add, add_zero]
          · have hne : index ≠ m.castSucc := by
              intro heq
              subst index
              simp at habove
            have hbelow : ¬ index.val < m.val := by omega
            have htail : m.castSucc.val < index.val := by
              simp only [Fin.val_castSucc]
              omega
            simp only [hbelow, if_false, hne, htail, if_true,
              zero_add]
    _ = N := b.sum_powers.symm

/-- The same three-way binary partition in the generic source-position
notation used by the induction. -/
public theorem lowerMass_add_current_add_tailMass (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    b.lowerMass m.castSucc + 2 ^ b.ell m.castSucc + b.tailMass m.castSucc = N := by
  simpa using b.prefixMass_add_current_add_tailMass m

/-- After stage `m`, the remaining binary mass is exactly the tail above
source bit `m`. -/
public theorem N_sub_lowerMass_succ_eq_tailMass (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    N - b.lowerMass m.succ = b.tailMass m.castSucc := by
  have hpartition := b.lowerMass_add_current_add_tailMass m
  rw [← b.lowerMass_succ m] at hpartition
  omega

/-- A later source block (including its own interval) lies entirely below an
earlier source block.  This is the finite-support ordering from which the
residual-block orthogonality follows. -/
public theorem tailMass_add_current_le_tailMass_of_lt (b : PositiveGapExpansion N)
    {left right : Fin (b.gaps + 1)} (hleft : left.val < right.val) :
    b.tailMass right + 2 ^ b.ell right ≤ b.tailMass left := by
  calc
    b.tailMass right + 2 ^ b.ell right =
        (∑ index : Fin (b.gaps + 1),
          if right.val < index.val then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.gaps + 1),
            if index = right then 2 ^ b.ell index else 0 := by
          simp [tailMass]
    _ = ∑ index : Fin (b.gaps + 1),
        ((if right.val < index.val then 2 ^ b.ell index else 0) +
          if index = right then 2 ^ b.ell index else 0) := by
          rw [Finset.sum_add_distrib]
    _ ≤ ∑ index : Fin (b.gaps + 1),
        if left.val < index.val then 2 ^ b.ell index else 0 := by
          apply Finset.sum_le_sum
          intro index _
          by_cases htail : right.val < index.val
          · have hleftIndex : left.val < index.val := lt_trans hleft htail
            have hne : index ≠ right := by
              intro heq
              subst index
              exact (Nat.lt_irrefl right.val) htail
            simp [htail, hleftIndex, hne]
          · by_cases hcurrent : index = right
            · subst index
              simp [hleft]
            · simp [htail, hcurrent]
    _ = b.tailMass left := by rfl

/-- Distinct source blocks have disjoint interval supports. -/
public theorem residualSupport_disjoint_of_lt (b : PositiveGapExpansion N)
    {left right : Fin (b.gaps + 1)} (hleft : left.val < right.val)
    (index : Nat) :
    ¬ (b.residualSupport left index ∧ b.residualSupport right index) := by
  intro hsupport
  rcases hsupport with ⟨hleftSupport, hrightSupport⟩
  have horder := b.tailMass_add_current_le_tailMass_of_lt hleft
  unfold residualSupport at hleftSupport hrightSupport
  omega
@[simp]
public theorem prefixMass_zero (b : PositiveGapExpansion N) :
    b.prefixMass ⟨0, b.gaps_pos⟩ = 0 := by
  unfold prefixMass
  simp

/-- The lower prefix together with its next source bit is bounded by the
certified binary sum.  This is the arithmetic fact that makes every source
rotation denominator positive. -/
public theorem prefixMass_add_current_le (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    b.prefixMass m + 2 ^ b.ell m.castSucc ≤ N := by
  calc
    b.prefixMass m + 2 ^ b.ell m.castSucc =
        (∑ index : Fin (b.gaps + 1),
          if index.val < m.val then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.gaps + 1),
            if index = m.castSucc then 2 ^ b.ell index else 0 := by
          simp [prefixMass]
    _ = ∑ index : Fin (b.gaps + 1),
        ((if index.val < m.val then 2 ^ b.ell index else 0) +
          if index = m.castSucc then 2 ^ b.ell index else 0) := by
          rw [Finset.sum_add_distrib]
    _ ≤ ∑ index : Fin (b.gaps + 1), 2 ^ b.ell index := by
          apply Finset.sum_le_sum
          intro index _
          by_cases hbelow : index.val < m.val
          · have hne : index ≠ m.castSucc := by
              intro heq
              subst index
              simp at hbelow
            simp [hbelow, hne]
          · by_cases hcurrent : index = m.castSucc
            · subst index
              simp
            · simp [hbelow, hcurrent]
    _ = N := b.sum_powers.symm

/-- Every Algorithm-1 rotation denominator is strictly positive. -/
public theorem prefixMass_lt (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    b.prefixMass m < N := by
  have hbound := b.prefixMass_add_current_le m
  have hpositive : 0 < 2 ^ b.ell m.castSucc := Nat.two_pow_pos _
  omega

/-- The squared retained amplitude used by one source rotation. -/
@[expose] public def sourceRatio (b : PositiveGapExpansion N) (m : Fin b.gaps) : ℝ :=
  ((2 ^ b.ell m.castSucc : Nat) : ℝ) /
    ((N - b.prefixMass m : Nat) : ℝ)

public theorem sourceRatio_nonneg (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    0 ≤ b.sourceRatio m := by
  unfold sourceRatio
  positivity

public theorem sourceRatio_le_one (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    b.sourceRatio m ≤ 1 := by
  have hsum := b.prefixMass_add_current_le m
  have hdenNat : 0 < N - b.prefixMass m := Nat.sub_pos_of_lt (b.prefixMass_lt m)
  have hnumNat : 2 ^ b.ell m.castSucc ≤ N - b.prefixMass m := by
    omega
  have hden : (0 : ℝ) < ((N - b.prefixMass m : Nat) : ℝ) := by
    exact_mod_cast hdenNat
  have hnum : ((2 ^ b.ell m.castSucc : Nat) : ℝ) ≤
      ((N - b.prefixMass m : Nat) : ℝ) := by
    exact_mod_cast hnumNat
  unfold sourceRatio
  apply (div_le_iff₀ hden).mpr
  simpa using hnum

/-- The real coefficient of the not-yet-opened aligned block at a source
position.  Its square is precisely the remaining binary mass divided by
`N`. -/
public def residualWeight (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1)) : ℝ :=
  Real.sqrt
    (((N - b.lowerMass m : Nat) : ℝ) / (N : ℝ))

/-- The real coefficient of one accepted aligned block.  Tensoring this
coefficient with its normalized Walsh block gives amplitude `1 / sqrt N` on
that block's support. -/
public def blockWeight (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1)) : ℝ :=
  Real.sqrt
    (((2 ^ b.ell m : Nat) : ℝ) / (N : ℝ))

@[simp]
public theorem residualWeight_nonneg (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1)) :
    0 ≤ b.residualWeight m :=
  Real.sqrt_nonneg _

@[simp]
public theorem blockWeight_nonneg (b : PositiveGapExpansion N) (m : Fin (b.gaps + 1)) :
    0 ≤ b.blockWeight m :=
  Real.sqrt_nonneg _

/-- The initial residual has unit coefficient. -/
public theorem residualWeight_zero (b : PositiveGapExpansion N) : b.residualWeight 0 = 1 := by
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt b.positive
  unfold residualWeight
  rw [b.lowerMass_zero, Nat.sub_zero, div_self hN, Real.sqrt_one]

/-- `sourceRatio` is the current summand divided by the residual mass in the
generic source-position notation. -/
public theorem sourceRatio_eq_current_over_residual (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    b.sourceRatio m =
      ((2 ^ b.ell m.castSucc : Nat) : ℝ) /
        ((N - b.lowerMass m.castSucc : Nat) : ℝ) := by
  simp [sourceRatio]

/-! The next two scalar lemmas isolate the only square-root algebra used by
the residual invariant.  They are real equalities; the circuit action later
uses their canonical coercions to complex amplitudes. -/

private theorem sqrt_mass_mul_sqrt_ratio (mass part total : Nat)
    (hmass : 0 < mass) (htotal : 0 < total) :
    Real.sqrt ((mass : ℝ) / (total : ℝ)) *
        Real.sqrt ((part : ℝ) / (mass : ℝ)) =
      Real.sqrt ((part : ℝ) / (total : ℝ)) := by
  have hmassReal : (mass : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hmass
  have htotalReal : (total : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htotal
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (mass : ℝ) / (total : ℝ))]
  congr 1
  field_simp [hmassReal, htotalReal]

private theorem sqrt_mass_mul_sqrt_complement (mass part total : Nat)
    (hmass : 0 < mass) (hpart : part ≤ mass) (htotal : 0 < total) :
    Real.sqrt ((mass : ℝ) / (total : ℝ)) *
        Real.sqrt (1 - (part : ℝ) / (mass : ℝ)) =
      Real.sqrt (((mass - part : Nat) : ℝ) / (total : ℝ)) := by
  have hmassReal : (mass : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hmass
  have htotalReal : (total : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htotal
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (mass : ℝ) / (total : ℝ))]
  congr 1
  rw [Nat.cast_sub hpart]
  field_simp [hmassReal, htotalReal]

/-- The Algorithm-1 rotation angle at one binary gap.  At `m = 0` its
denominator is `N`, since the prefix mass is empty. -/
@[expose] public def sourceAngle (b : PositiveGapExpansion N) (m : Fin b.gaps) : ℝ :=
  -2 * Real.arccos
    (Real.sqrt (b.sourceRatio m))

/-- The `|1⟩` coefficient retained by the source rotation is the square root
of its declared binary-mass ratio. -/
public theorem cos_half_sourceAngle (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    Real.cos (b.sourceAngle m / 2) = Real.sqrt (b.sourceRatio m) := by
  have hnonneg := b.sourceRatio_nonneg m
  have hsqrt_nonneg : 0 ≤ Real.sqrt (b.sourceRatio m) := Real.sqrt_nonneg _
  have hsqrt_le_one : Real.sqrt (b.sourceRatio m) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · simpa using b.sourceRatio_le_one m
  unfold sourceAngle
  rw [show (-2 * Real.arccos (Real.sqrt (b.sourceRatio m))) / 2 =
      -Real.arccos (Real.sqrt (b.sourceRatio m)) by ring,
    Real.cos_neg,
    Real.cos_arccos (by linarith) hsqrt_le_one]

/-- The newly opened residual coefficient is the complementary square root.
The negation is exactly the sign appearing in `R_Y(θ)|1⟩`. -/
public theorem neg_sin_half_sourceAngle (b : PositiveGapExpansion N) (m : Fin b.gaps) :
    -(Real.sin (b.sourceAngle m / 2)) =
      Real.sqrt (1 - b.sourceRatio m) := by
  have hnonneg := b.sourceRatio_nonneg m
  unfold sourceAngle
  rw [show (-2 * Real.arccos (Real.sqrt (b.sourceRatio m))) / 2 =
      -Real.arccos (Real.sqrt (b.sourceRatio m)) by ring,
    Real.sin_neg, neg_neg, Real.sin_arccos,
    Real.sq_sqrt hnonneg]

/-- The retained branch of a source rotation has exactly the accepted-block
coefficient required by the binary partition. -/
public theorem residualWeight_mul_cos_half_sourceAngle (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    b.residualWeight m.castSucc * Real.cos (b.sourceAngle m / 2) =
      b.blockWeight m.castSucc := by
  rw [b.cos_half_sourceAngle, b.sourceRatio_eq_current_over_residual]
  have hmass : 0 < N - b.lowerMass m.castSucc := by
    rw [b.lowerMass_castSucc]
    exact Nat.sub_pos_of_lt (b.prefixMass_lt m)
  simpa [residualWeight, blockWeight] using
    (sqrt_mass_mul_sqrt_ratio
      (N - b.lowerMass m.castSucc) (2 ^ b.ell m.castSucc) N hmass b.positive)

/-- The opened branch of a source rotation has the residual coefficient at
the next source position. -/
public theorem residualWeight_mul_neg_sin_half_sourceAngle (b : PositiveGapExpansion N)
    (m : Fin b.gaps) :
    b.residualWeight m.castSucc * (-(Real.sin (b.sourceAngle m / 2))) =
      b.residualWeight m.succ := by
  rw [b.neg_sin_half_sourceAngle, b.sourceRatio_eq_current_over_residual]
  have hmass : 0 < N - b.lowerMass m.castSucc := by
    rw [b.lowerMass_castSucc]
    exact Nat.sub_pos_of_lt (b.prefixMass_lt m)
  have hpart : 2 ^ b.ell m.castSucc ≤ N - b.lowerMass m.castSucc := by
    rw [b.lowerMass_castSucc]
    have hsum := b.prefixMass_add_current_le m
    omega
  have htail :
      (N - b.lowerMass m.castSucc) - 2 ^ b.ell m.castSucc =
        N - b.lowerMass m.succ := by
    rw [Nat.sub_sub, ← b.lowerMass_succ m]
  have hscalar := sqrt_mass_mul_sqrt_complement
      (N - b.lowerMass m.castSucc) (2 ^ b.ell m.castSucc) N
      hmass hpart b.positive
  rw [htail] at hscalar
  simpa [residualWeight] using hscalar

/-- The number of source bit positions opened by one strict binary gap. -/
public def gapWidth (b : PositiveGapExpansion N) (gap : Fin b.gaps) : Nat :=
  b.ell gap.succ - b.ell gap.castSucc
/-- Extend the finite source exponent sequence by its final value.  This
auxiliary monotone function exposes the natural-number telescoping lemma for
the literal gap widths. -/
public def clampedEll (b : PositiveGapExpansion N) (index : Nat) : Nat :=
  b.ell ⟨min index b.gaps, by
    have hle : min index b.gaps ≤ b.gaps := Nat.min_le_right _ _
    omega⟩

private theorem clampedEll_monotone (b : PositiveGapExpansion N) :
    Monotone b.clampedEll := by
  intro left right hleft
  apply b.ell_strict.monotone
  change min left b.gaps ≤ min right b.gaps
  exact min_le_min hleft le_rfl

@[simp]
private theorem clampedEll_zero (b : PositiveGapExpansion N) :
    b.clampedEll 0 = b.first := by
  simp [clampedEll, first]

@[simp]
private theorem clampedEll_last (b : PositiveGapExpansion N) :
    b.clampedEll b.gaps = b.last := by
  unfold clampedEll last
  congr 1
  apply Fin.ext
  simp

/-- Strict source gaps telescope exactly to the interval between the lowest
and highest set-bit exponents. -/
public theorem sum_gapWidth (b : PositiveGapExpansion N) :
    ∑ gap : Fin b.gaps, b.gapWidth gap = b.last - b.first := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ index ∈ Finset.range b.gaps,
        (b.clampedEll (index + 1) - b.clampedEll index) := by
      apply Finset.sum_congr rfl
      intro index hindex
      have hlt : index < b.gaps := Finset.mem_range.mp hindex
      simp only [dif_pos hlt]
      change b.gapWidth (Fin.mk index hlt) = _
      simp [gapWidth, clampedEll, Nat.min_eq_left (Nat.le_of_lt hlt),
        Nat.min_eq_left (Nat.succ_le_iff.mpr hlt)]
    _ = b.clampedEll b.gaps - b.clampedEll 0 :=
      Finset.sum_range_tsub (b.clampedEll_monotone) b.gaps
    _ = b.last - b.first := by simp

/-- Because every source gap is strict, the number of gaps is no larger than
their total width. -/
public theorem gaps_le_gapWidth_sum (b : PositiveGapExpansion N) :
    b.gaps ≤ ∑ gap : Fin b.gaps, b.gapWidth gap := by
  calc
    b.gaps = ∑ _gap : Fin b.gaps, 1 := by simp
    _ ≤ ∑ gap : Fin b.gaps, b.gapWidth gap := by
      apply Finset.sum_le_sum
      intro gap _
      unfold gapWidth
      have hstrict : b.ell gap.castSucc < b.ell gap.succ :=
        b.ell_strict gap.castSucc_lt_succ
      omega

end

end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
