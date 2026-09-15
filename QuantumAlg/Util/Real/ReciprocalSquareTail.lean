/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Analysis.PSeries

/-!
# Finite reciprocal-square tails

This file isolates the quantum-free estimate used by the high-confidence phase
estimation analysis.  A reciprocal-square progression is bounded by its first
term plus a telescoping reciprocal tail.  The integer version splits a finite
set about `floor x`, giving the two tails that occur on a cyclic phase grid.
-/

section

namespace QuantumAlg

noncomputable section

/-- Thin real specialization of Mathlib's finite reciprocal-square tail. -/
theorem reciprocalSquareNatFiniteTail_le (k n : Nat) (hk : 0 < k)
    (hkn : k <= n) :
    (∑ i ∈ Finset.Ioc k n, 1 / (i : Real) ^ 2) <= 1 / (k : Real) := by
  have htail :=
    sum_Ioc_inv_sq_le_sub (α := Real) hk.ne' hkn
  calc
    (∑ i ∈ Finset.Ioc k n, 1 / (i : Real) ^ 2) =
        ∑ i ∈ Finset.Ioc k n, (((i : Real) ^ 2)⁻¹) := by
      simp only [one_div]
    _ <= ((k : Real)⁻¹ - (n : Real)⁻¹) := htail
    _ <= (k : Real)⁻¹ :=
      sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = 1 / (k : Real) := by simp only [one_div]

private theorem reciprocalSquare_succ_le_telescope (x : Real) (hx : 0 < x) :
    1 / (x + 1) ^ 2 <= 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hsub : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp [ne_of_gt hx, ne_of_gt hx1]
    ring
  rw [hsub]
  apply one_div_le_one_div_of_le (mul_pos hx hx1)
  nlinarith [sq_nonneg (x + 1)]

/-- A finite reciprocal-square progression with positive real first term is at
most its first term plus the corresponding infinite telescoping envelope. -/
theorem reciprocalSquareShiftedFiniteTail_le (a : Real) (n : Nat)
    (ha : 0 < a) :
    (∑ k ∈ Finset.range n, 1 / (a + (k : Real)) ^ 2) <=
      1 / a ^ 2 + 1 / a := by
  cases n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, add_zero]
      have htail :
          (∑ k ∈ Finset.range n,
              1 / (a + ((k + 1 : Nat) : Real)) ^ 2) <=
            ∑ k ∈ Finset.range n,
              (1 / (a + (k : Real)) -
                1 / (a + ((k + 1 : Nat) : Real))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hx : 0 < a + (k : Real) := by positivity
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
          reciprocalSquare_succ_le_telescope (a + (k : Real)) hx
      calc
        (∑ k ∈ Finset.range n,
              1 / (a + ((k + 1 : Nat) : Real)) ^ 2) +
            1 / a ^ 2 <=
          (∑ k ∈ Finset.range n,
              (1 / (a + (k : Real)) -
                1 / (a + ((k + 1 : Nat) : Real)))) +
            1 / a ^ 2 := by
          simpa using add_le_add_right htail (1 / a ^ 2)
        _ = 1 / a ^ 2 + (1 / a - 1 / (a + (n : Real))) := by
          rw [Finset.sum_range_sub']
          simp
          ring
        _ <= 1 / a ^ 2 + 1 / a := by
          have hnonneg : 0 <= 1 / (a + (n : Real)) := by positivity
          simpa [add_comm] using add_le_add_left
            (sub_le_self (1 / a) hnonneg) (1 / a ^ 2)

private theorem reciprocalSquareShiftedSubset_le
    (s : Finset Nat) (a ρ : Real) (hrho : 0 < ρ)
    (hfar : ∀ k ∈ s, ρ <= a + (k : Real)) :
    (∑ k ∈ s, 1 / (a + (k : Real)) ^ 2) <=
      1 / ρ ^ 2 + 1 / ρ := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp only [Finset.sum_empty]
    positivity
  let first := s.min' (Finset.nonempty_iff_ne_empty.mpr hs)
  let last := s.max' (Finset.nonempty_iff_ne_empty.mpr hs)
  have hfirst_mem : first ∈ s := by
    exact Finset.min'_mem s (Finset.nonempty_iff_ne_empty.mpr hs)
  have hfirst : ρ <= a + (first : Real) := hfar first hfirst_mem
  have hfirst_pos : 0 < a + (first : Real) := hrho.trans_le hfirst
  have hsubset : s ⊆ Finset.Icc first last := by
    intro k hk
    exact Finset.mem_Icc.mpr
      (And.intro (Finset.min'_le s k hk) (Finset.le_max' s k hk))
  calc
    (∑ k ∈ s, 1 / (a + (k : Real)) ^ 2) <=
        ∑ k ∈ Finset.Icc first last, 1 / (a + (k : Real)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k hkIcc hks
      positivity
    _ = ∑ offset ∈ Finset.range (last + 1 - first),
          1 / ((a + (first : Real)) + (offset : Real)) ^ 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro offset hoffset
      congr 2
      push_cast
      ring
    _ <= 1 / (a + (first : Real)) ^ 2 +
          1 / (a + (first : Real)) :=
      reciprocalSquareShiftedFiniteTail_le
        (a + (first : Real)) (last + 1 - first) hfirst_pos
    _ <= 1 / ρ ^ 2 + 1 / ρ := by
      apply add_le_add
      · apply one_div_le_one_div_of_le (pow_pos hrho 2)
        exact (sq_le_sq₀ hrho.le hfirst_pos.le).2 hfirst
      · exact one_div_le_one_div_of_le hrho hfirst

/-- Two-sided finite integer reciprocal-square tail.  The first point on each
side contributes the endpoint term and the remaining points are bounded by
`reciprocalSquareShiftedFiniteTail_le`. -/
theorem integerReciprocalSquareTail_le (s : Finset Int) (x ρ : Real)
    (hrho : 0 < ρ)
    (hfar : ∀ z ∈ s, ρ <= |x - (z : Real)|) :
    (∑ z ∈ s, 1 / |x - (z : Real)| ^ 2) <=
      2 / ρ + 2 / ρ ^ 2 := by
  classical
  let base : Int := Int.floor x
  let left := s.filter (fun z => z <= base)
  let right := s.filter (fun z => base < z)
  let leftOffset : Int -> Nat := fun z => (base - z).toNat
  let rightOffset : Int -> Nat := fun z => (z - (base + 1)).toNat
  let leftOffsets := left.image leftOffset
  let rightOffsets := right.image rightOffset
  have hfrac_nonneg : 0 <= x - (base : Real) := by
    dsimp [base]
    exact sub_nonneg.mpr (Int.floor_le x)
  have hfrac_lt : x - (base : Real) < 1 := by
    dsimp [base]
    exact Int.fract_lt_one x
  have hleftOffset_injective : Set.InjOn leftOffset left := by
    intro z hz w hw hzw
    have hzle : z <= base := (Finset.mem_filter.mp hz).2
    have hwle : w <= base := (Finset.mem_filter.mp hw).2
    have hznonneg : 0 <= base - z := sub_nonneg.mpr hzle
    have hwnonneg : 0 <= base - w := sub_nonneg.mpr hwle
    have hcast : base - z = base - w := by
      rw [← Int.toNat_of_nonneg hznonneg,
        ← Int.toNat_of_nonneg hwnonneg]
      exact_mod_cast hzw
    omega
  have hrightOffset_injective : Set.InjOn rightOffset right := by
    intro z hz w hw hzw
    have hzgt : base < z := (Finset.mem_filter.mp hz).2
    have hwgt : base < w := (Finset.mem_filter.mp hw).2
    have hznonneg : 0 <= z - (base + 1) := by omega
    have hwnonneg : 0 <= w - (base + 1) := by omega
    have hcast : z - (base + 1) = w - (base + 1) := by
      rw [← Int.toNat_of_nonneg hznonneg,
        ← Int.toNat_of_nonneg hwnonneg]
      exact_mod_cast hzw
    omega
  have hleft_sum :
      (∑ z ∈ left, 1 / |x - (z : Real)| ^ 2) =
        ∑ k ∈ leftOffsets,
          1 / ((x - (base : Real)) + (k : Real)) ^ 2 := by
    rw [Finset.sum_image hleftOffset_injective]
    apply Finset.sum_congr rfl
    intro z hz
    have hzle : z <= base := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= base - z := sub_nonneg.mpr hzle
    rw [abs_of_nonneg]
    · congr 2
      have hoffsetCast :
          (((base - z).toNat : Nat) : Real) = ((base - z : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · exact sub_nonneg.mpr (by
        have hzcast : (z : Real) <= (base : Real) := by
          exact_mod_cast hzle
        have hfloor : (base : Real) <= x := by
          simpa [base] using Int.floor_le x
        exact hzcast.trans hfloor)
  have hright_sum :
      (∑ z ∈ right, 1 / |x - (z : Real)| ^ 2) =
        ∑ k ∈ rightOffsets,
          1 / ((((base + 1 : Int) : Real) - x) + (k : Real)) ^ 2 := by
    rw [Finset.sum_image hrightOffset_injective]
    apply Finset.sum_congr rfl
    intro z hz
    have hzgt : base < z := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= z - (base + 1) := by omega
    rw [abs_of_nonpos]
    · congr 2
      have hoffsetCast :
          (((z - (base + 1)).toNat : Nat) : Real) =
            ((z - (base + 1) : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · exact sub_nonpos.mpr (by
        have hxlt : x < ((base + 1 : Int) : Real) := by
          simpa only [base, Int.cast_add, Int.cast_one] using
            Int.lt_floor_add_one x
        have hstep : ((base + 1 : Int) : Real) <= (z : Real) := by
          exact_mod_cast (Int.add_one_le_iff.mpr hzgt)
        exact hxlt.le.trans hstep)
  have hleft_far :
      ∀ k ∈ leftOffsets, ρ <= (x - (base : Real)) + (k : Real) := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    have hzmem : z ∈ s := (Finset.mem_filter.mp hz).1
    have hzle : z <= base := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= base - z := sub_nonneg.mpr hzle
    convert hfar z hzmem using 1
    rw [abs_of_nonneg]
    · have hoffsetCast :
          (((base - z).toNat : Nat) : Real) = ((base - z : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · exact sub_nonneg.mpr (by
        have hfloor : (base : Real) <= x := by
          simpa [base] using Int.floor_le x
        have hzcast : (z : Real) <= (base : Real) := by
          exact_mod_cast hzle
        exact hzcast.trans hfloor)
  have hright_far :
      ∀ k ∈ rightOffsets,
        ρ <= (((base + 1 : Int) : Real) - x) + (k : Real) := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    have hzmem : z ∈ s := (Finset.mem_filter.mp hz).1
    have hzgt : base < z := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= z - (base + 1) := by omega
    convert hfar z hzmem using 1
    rw [abs_of_nonpos]
    · have hoffsetCast :
          (((z - (base + 1)).toNat : Nat) : Real) =
            ((z - (base + 1) : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · have hxlt : x < ((base + 1 : Int) : Real) := by
        simpa only [base, Int.cast_add, Int.cast_one] using
          Int.lt_floor_add_one x
      have hstep : ((base + 1 : Int) : Real) <= (z : Real) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hzgt)
      exact sub_nonpos.mpr
        (hxlt.le.trans hstep)
  have hleft_bound := reciprocalSquareShiftedSubset_le leftOffsets
    (x - (base : Real)) ρ hrho hleft_far
  have hright_bound := reciprocalSquareShiftedSubset_le rightOffsets
    (((base + 1 : Int) : Real) - x) ρ hrho hright_far
  have hsplit :
      (∑ z ∈ s, 1 / |x - (z : Real)| ^ 2) =
        (∑ z ∈ left, 1 / |x - (z : Real)| ^ 2) +
          ∑ z ∈ right, 1 / |x - (z : Real)| ^ 2 := by
    have hright_filter :
        right = s.filter (fun z : Int => ¬ z <= base) := by
      ext z
      simp [right]
    rw [hright_filter]
    dsimp [left]
    exact (Finset.sum_filter_add_sum_filter_not s
      (fun z : Int => z <= base)
      (fun z => 1 / |x - (z : Real)| ^ 2)).symm
  rw [hsplit, hleft_sum, hright_sum]
  calc
    (∑ k ∈ leftOffsets,
          1 / ((x - (base : Real)) + (k : Real)) ^ 2) +
        ∑ k ∈ rightOffsets,
          1 / ((((base + 1 : Int) : Real) - x) + (k : Real)) ^ 2 <=
      (1 / ρ ^ 2 + 1 / ρ) + (1 / ρ ^ 2 + 1 / ρ) :=
        add_le_add hleft_bound hright_bound
    _ = 2 / ρ + 2 / ρ ^ 2 := by ring

end

end QuantumAlg

end
