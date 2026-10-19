/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Finite pivot reflections and modular offset

A pivot flip reverses the labels below its pivot and fixes the others.
The corresponding bi-flip reflects both intervals independently. These
quantum-free identities include pivots zero and equal to the full capacity
[G17, paper.tex:266-293]. Three pivot flips implement a modular offset
and fix labels outside its residue range [G17, paper.tex:319-334].
No parity or invertibility hypothesis is needed for this additive identity.
-/

namespace QuantumAlg.Nat.FixedWidth

/-- Reverse the interval below `pivot`, fixing every other natural label. -/
def pivotFlip (pivot input : Nat) : Nat :=
  if input < pivot then pivot - (input + 1) else input

/-- Reflect both intervals separated by the pivot inside the declared capacity. -/
def biFlip (capacity pivot input : Nat) : Nat :=
  if input < pivot then pivot - (input + 1) else capacity + pivot - (input + 1)

/-- Labels below the pivot stay below it. -/
lemma pivotFlip_lt_of_lt {pivot input : Nat} (h : input < pivot) :
    pivotFlip pivot input < pivot := by
  simp only [pivotFlip, if_pos h]
  omega

/-- Every label at or above the pivot is fixed. -/
lemma pivotFlip_of_le {pivot input : Nat} (h : pivot ≤ input) :
    pivotFlip pivot input = input := by
  simp only [pivotFlip, if_neg (by omega : ¬input < pivot)]

/-- Pivot reflection is an involution on all natural labels. -/
lemma pivotFlip_involutive (pivot input : Nat) :
    pivotFlip pivot (pivotFlip pivot input) = input := by
  by_cases h : input < pivot
  · have hnext : pivot - (input + 1) < pivot := by omega
    simp only [pivotFlip, if_pos h, if_pos hnext]
    omega
  · simp only [pivotFlip, if_neg h]

/-- A pivot fitting inside the carrier preserves the carrier. -/
lemma pivotFlip_lt_capacity {capacity pivot input : Nat}
    (hpivot : pivot ≤ capacity) (hinput : input < capacity) :
    pivotFlip pivot input < capacity := by
  by_cases h : input < pivot
  · exact lt_of_lt_of_le (pivotFlip_lt_of_lt h) hpivot
  · simpa only [pivotFlip, if_neg h] using hinput

/-- The bi-flip preserves both sides of the pivot, including its endpoints. -/
lemma biFlip_lt_pivot_iff {capacity pivot input : Nat}
    (_hpivot : pivot ≤ capacity) (hinput : input < capacity) :
    biFlip capacity pivot input < pivot ↔ input < pivot := by
  by_cases h : input < pivot
  · simp only [biFlip, if_pos h]
    omega
  · simp only [biFlip, if_neg h]
    omega

/-- The bi-flip stays inside the same finite carrier. -/
lemma biFlip_lt_capacity {capacity pivot input : Nat}
    (hpivot : pivot ≤ capacity) (hinput : input < capacity) :
    biFlip capacity pivot input < capacity := by
  by_cases h : input < pivot
  · simp only [biFlip, if_pos h]
    omega
  · simp only [biFlip, if_neg h]
    omega

/-- Applying the bi-flip twice restores every in-range label. -/
lemma biFlip_involutive {capacity pivot input : Nat}
    (_hpivot : pivot ≤ capacity) (hinput : input < capacity) :
    biFlip capacity pivot (biFlip capacity pivot input) = input := by
  by_cases h : input < pivot
  · have hnext : pivot - (input + 1) < pivot := by omega
    simp only [biFlip, if_pos h, if_pos hnext]
    omega
  · have hnext : ¬capacity + pivot - (input + 1) < pivot := by omega
    simp only [biFlip, if_neg h, if_neg hnext]
    omega

/-- Subtracting the pivot modulo the capacity and complementing is the bi-flip. -/
lemma biFlip_eq_complement_sub_mod {capacity pivot input : Nat}
    (hpivot : pivot ≤ capacity) (hinput : input < capacity) :
    biFlip capacity pivot input =
      capacity - ((input + (capacity - pivot) % capacity) % capacity + 1) := by
  rw [Nat.add_mod_mod]
  by_cases h : input < pivot
  · have hsum : input + (capacity - pivot) < capacity := by omega
    rw [Nat.mod_eq_of_lt hsum]
    simp only [biFlip, if_pos h]
    omega
  · have hsum : capacity ≤ input + (capacity - pivot) := by omega
    have hsmall : input + (capacity - pivot) - capacity < capacity := by omega
    rw [Nat.mod_eq_sub_mod hsum, Nat.mod_eq_of_lt hsmall]
    simp only [biFlip, if_neg h]
    omega

/-- Three reflections give the canonical offset inside the modulus and fix its complement. -/
lemma pivotFlip_three_eq_modular_offset {modulus constant input : Nat}
    (hconstant : constant ≤ modulus) :
    pivotFlip constant (pivotFlip modulus (pivotFlip (modulus - constant) input)) =
      if input < modulus then (input + constant) % modulus else input := by
  by_cases hvalid : input < modulus
  · rw [if_pos hvalid]
    by_cases hwrap : input < modulus - constant
    · have hfirst : pivotFlip (modulus - constant) input =
          modulus - constant - (input + 1) := by
        simp only [pivotFlip, if_pos hwrap]
      have hmiddle : modulus - constant - (input + 1) < modulus := by omega
      have hsecond : modulus - (modulus - constant - (input + 1) + 1) =
          input + constant := by omega
      have hlast : ¬input + constant < constant := by omega
      have hsum : input + constant < modulus := by omega
      rw [hfirst]
      simp only [pivotFlip, if_pos hmiddle, hsecond, if_neg hlast,
        Nat.mod_eq_of_lt hsum]
    · have hfirst : pivotFlip (modulus - constant) input = input := by
        simp only [pivotFlip, if_neg hwrap]
      have hmiddle : modulus - (input + 1) < constant := by omega
      have hsum : modulus ≤ input + constant := by omega
      have hsmall : input + constant - modulus < modulus := by omega
      rw [hfirst]
      simp only [pivotFlip, if_pos hvalid, if_pos hmiddle,
        Nat.mod_eq_sub_mod hsum, Nat.mod_eq_of_lt hsmall]
      omega
  · have hfirst : ¬input < modulus - constant := by omega
    have hlast : ¬input < constant := by omega
    simp only [pivotFlip, if_neg hfirst, if_neg hvalid, if_neg hlast]

/-- Zero modulus has no valid labels and the three-flip extension is identity. -/
lemma pivotFlip_zero (input : Nat) : pivotFlip 0 input = input := by
  simp only [pivotFlip, Nat.not_lt_zero, if_false]

/-- Modulus one is included: its unique valid label is preserved. -/
lemma pivotFlip_modulus_one {constant : Nat} (hconstant : constant ≤ 1) :
    pivotFlip constant (pivotFlip 1 (pivotFlip (1 - constant) 0)) = 0 := by
  rw [pivotFlip_three_eq_modular_offset hconstant]
  simp [Nat.mod_one]

end QuantumAlg.Nat.FixedWidth
