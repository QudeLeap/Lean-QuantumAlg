/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting
import QuantumAlg.Init

/-!
# A finite common-divisor tail bound

This module bounds pairs of positive integers below `X` whose gcd is at least
`D`.  It deliberately counts all integers, so later prime-pair applications do
not require any equidistribution theorem for primes in arithmetic progressions.
-/

section

namespace QuantumAlg
namespace NumberTheory

open Finset

/-- Positive multiples of `d` strictly below `X`. -/
def positiveMultiplesBelow (X d : Nat) : Finset Nat :=
  (Finset.range X).filter fun n => n ≠ 0 ∧ d ∣ n

/-- An explicit union covering every positive pair below `X` whose gcd is at
least `D`. -/
def commonDivisorPairs (X D : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc D (X - 1)).biUnion fun d =>
    (positiveMultiplesBelow X d).product (positiveMultiplesBelow X d)

theorem card_positiveMultiplesBelow (X d : Nat) (hX : 0 < X) :
    (positiveMultiplesBelow X d).card = (X - 1) / d := by
  unfold positiveMultiplesBelow
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ X)] using
    Nat.card_multiples' (X - 1) d

/-- A positive bounded pair with gcd at least `D` belongs to the explicit
common-multiple union. -/
theorem mem_commonDivisorPairs {X D a b : Nat}
    (haPos : 0 < a) (hbPos : 0 < b)
    (haLt : a < X) (hbLt : b < X)
    (hlarge : D ≤ Nat.gcd a b) :
    (a, b) ∈ commonDivisorPairs X D := by
  have hgcdPos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b haPos
  have hgcdLe : Nat.gcd a b ≤ X - 1 := by
    have hleA : Nat.gcd a b ≤ a :=
      Nat.le_of_dvd haPos (Nat.gcd_dvd_left a b)
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨Nat.gcd a b, Finset.mem_Icc.mpr ⟨hlarge, hgcdLe⟩, ?_⟩
  apply Finset.mem_product.mpr
  constructor <;>
    simp only [positiveMultiplesBelow, Finset.mem_filter,
      Finset.mem_range, ne_eq]
  · exact ⟨haLt, haPos.ne', Nat.gcd_dvd_left a b⟩
  · exact ⟨hbLt, hbPos.ne', Nat.gcd_dvd_right a b⟩

/-- The elementary square-summable union bound.  The factor `2` is the
standard tail estimate `sum_{d≥D} 1/d² ≤ 2/D`. -/
theorem commonDivisorPairs_card_bound (X D : Nat) (hX : 0 < X)
    (hD : 0 < D) :
    (D : Real) * (commonDivisorPairs X D).card ≤ 2 * (X : Real) ^ 2 := by
  have hcardNat :
      (commonDivisorPairs X D).card ≤
        ∑ d ∈ Finset.Icc D (X - 1), ((X - 1) / d) ^ 2 := by
    unfold commonDivisorPairs
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro d _hd
    change #((positiveMultiplesBelow X d) ×ˢ
      (positiveMultiplesBelow X d)) ≤ ((X - 1) / d) ^ 2
    rw [Finset.card_product (positiveMultiplesBelow X d)
      (positiveMultiplesBelow X d),
      card_positiveMultiplesBelow X d hX, pow_two]
  have hcardReal :
      ((commonDivisorPairs X D).card : Real) ≤
        ∑ d ∈ Finset.Icc D (X - 1),
          (((X - 1) / d : Nat) : Real) ^ 2 := by
    exact_mod_cast hcardNat
  have hterm (d : Nat) (hd : d ∈ Finset.Icc D (X - 1)) :
      ((((X - 1) / d : Nat) : Real) ^ 2) ≤
        (X : Real) ^ 2 * ((d : Real) ^ 2)⁻¹ := by
    have hdPos : 0 < d := hD.trans_le (Finset.mem_Icc.mp hd).1
    have hquot : (((X - 1) / d : Nat) : Real) ≤ (X : Real) / d := by
      exact Nat.cast_div_le.trans <|
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le X 1)
          (Nat.cast_nonneg d)
    have hquotNonneg : 0 ≤ (((X - 1) / d : Nat) : Real) := by positivity
    have hdivNonneg : 0 ≤ (X : Real) / d := by positivity
    calc
      (((X - 1) / d : Nat) : Real) ^ 2 ≤ ((X : Real) / d) ^ 2 :=
        pow_le_pow_left₀ hquotNonneg hquot 2
      _ = (X : Real) ^ 2 * ((d : Real) ^ 2)⁻¹ := by
        field_simp
  have hsum :
      (∑ d ∈ Finset.Icc D (X - 1),
          (((X - 1) / d : Nat) : Real) ^ 2) ≤
        (X : Real) ^ 2 * (2 / D) := by
    calc
      (∑ d ∈ Finset.Icc D (X - 1),
          (((X - 1) / d : Nat) : Real) ^ 2) ≤
          ∑ d ∈ Finset.Icc D (X - 1),
            (X : Real) ^ 2 * ((d : Real) ^ 2)⁻¹ := by
              exact Finset.sum_le_sum fun d hd => hterm d hd
      _ = (X : Real) ^ 2 *
          ∑ d ∈ Finset.Icc D (X - 1), ((d : Real) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]
      _ ≤ (X : Real) ^ 2 * (2 / D) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hinterval : Finset.Icc D (X - 1) = Finset.Ioo (D - 1) X := by
          ext d
          simp only [Finset.mem_Icc, Finset.mem_Ioo]
          omega
        rw [hinterval]
        have htail :
            (∑ d ∈ Finset.Ioo (D - 1) X, ((d : Real) ^ 2)⁻¹) ≤
              2 / (((D - 1 : Nat) : Real) + 1) :=
          sum_Ioo_inv_sq_le (D - 1) X
        have hcast : (((D - 1 : Nat) : Real) + 1) = D := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ D))
        rw [hcast] at htail
        exact htail
  have hbound := hcardReal.trans hsum
  have hDReal : (0 : Real) < D := by exact_mod_cast hD
  calc
    (D : Real) * (commonDivisorPairs X D).card ≤
        (D : Real) * ((X : Real) ^ 2 * (2 / D)) :=
      mul_le_mul_of_nonneg_left hbound hDReal.le
    _ = 2 * (X : Real) ^ 2 := by field_simp

end NumberTheory
end QuantumAlg

end
