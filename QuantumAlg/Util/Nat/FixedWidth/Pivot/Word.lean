/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Flip
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Bool.Basic

/-!
# Finite pivot reflections, dirty-control cancellation, and modular offset

These quantum-free functions specify finite-word outputs independently of
any circuit. Bi-flips preserve the pivot predicate and are involutions;
the four Boolean-controlled actions return an arbitrary initial control
[G17, paper.tex:266-293]. Three pivot flips implement canonical modular
addition and fix every remaining binary label [G17, paper.tex:319-334].
Zero constants, modulus one, even moduli, and full-capacity moduli are
included without parity or invertibility assumptions.
-/

namespace QuantumAlg.Nat.FixedWidth

/-- The independent finite pivot-reflection output for every fitted pivot. -/
def pivotWordOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (input : Fin (2 ^ width)) : Fin (2 ^ width) :=
  ⟨pivotFlip pivot.val input.val,
    pivotFlip_lt_capacity (by have := pivot.isLt; omega) input.isLt⟩

/-- Reflect both sides of a fitted pivot inside the same finite target word. -/
def biFlipWordOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (input : Fin (2 ^ width)) : Fin (2 ^ width) :=
  ⟨biFlip (2 ^ width) pivot.val input.val,
    biFlip_lt_capacity (by have := pivot.isLt; omega) input.isLt⟩

lemma gidneyBiFlipWord_involutive {width : Nat} (pivot : Fin (2 ^ width + 1))
    (input : Fin (2 ^ width)) :
    biFlipWordOutput pivot (biFlipWordOutput pivot input) = input := by
  apply Fin.ext
  exact biFlip_involutive (by have := pivot.isLt; omega) input.isLt

lemma gidneyBiFlipWord_compare {width : Nat} (pivot : Fin (2 ^ width + 1))
    (input : Fin (2 ^ width)) :
    decide ((biFlipWordOutput pivot input).val < pivot.val) =
      decide (input.val < pivot.val) := by
  congr 1
  exact propext (biFlip_lt_pivot_iff
    (by have := pivot.isLt; omega) input.isLt)

lemma gidneyBiFlipWord_of_lt {width : Nat} (pivot : Fin (2 ^ width + 1))
    (input : Fin (2 ^ width)) (h : input.val < pivot.val) :
    biFlipWordOutput pivot input = pivotWordOutput pivot input := by
  apply Fin.ext
  simp only [biFlipWordOutput, pivotWordOutput, biFlip,
    pivotFlip, if_pos h]

lemma gidneyPivotWord_of_le {width : Nat} (pivot : Fin (2 ^ width + 1))
    (input : Fin (2 ^ width)) (h : pivot.val ≤ input.val) :
    pivotWordOutput pivot input = input := by
  apply Fin.ext
  exact pivotFlip_of_le h

/-- Preserve the flag, conditionally applying the exact finite bi-flip. -/
def biFlipFlagStep {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Bool × Fin (2 ^ width)) : Bool × Fin (2 ^ width) :=
  (state.1, if state.1 then biFlipWordOutput pivot state.2 else state.2)

/-- Xor the predicate into a flag of arbitrary initial value. -/
def compareFlagStep {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Bool × Fin (2 ^ width)) : Bool × Fin (2 ^ width) :=
  (state.1 ^^ decide (state.2.val < pivot.val), state.2)

/-- The four exact actions produce a pivot reflection and return the original dirty flag. -/
lemma gidneyBiFlip_four_steps {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Bool × Fin (2 ^ width)) :
    compareFlagStep pivot (biFlipFlagStep pivot
        (compareFlagStep pivot (biFlipFlagStep pivot state))) =
      (state.1, pivotWordOutput pivot state.2) := by
  rcases state with ⟨flag, input⟩
  have hcompare := gidneyBiFlipWord_compare pivot input
  cases flag <;> by_cases hlt : input.val < pivot.val
  · have hword := gidneyBiFlipWord_of_lt pivot input hlt
    simp only [biFlipFlagStep, compareFlagStep, Bool.false_eq_true, if_false,
      decide_eq_true hlt, Bool.false_xor, if_true, hcompare, Bool.xor_self]
    exact congrArg (fun word => (false, word)) hword
  · have hword := gidneyPivotWord_of_le pivot input (by omega)
    simp only [biFlipFlagStep, compareFlagStep, Bool.false_eq_true, if_false,
      decide_eq_false hlt, Bool.false_xor, hword]
  · have hword := gidneyBiFlipWord_of_lt pivot input hlt
    simp only [biFlipFlagStep, compareFlagStep, if_true, hcompare,
      decide_eq_true hlt, Bool.xor_self, Bool.false_eq_true, if_false, Bool.false_xor]
    exact congrArg (fun word => (true, word)) hword
  · have hword := gidneyPivotWord_of_le pivot input (by omega)
    simp only [biFlipFlagStep, compareFlagStep, if_true, hcompare,
      decide_eq_false hlt, Bool.xor_false, gidneyBiFlipWord_involutive, hword]


/-- Canonical modular offset, extended by identity on the unused binary labels. -/
def modularWordOutput {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (input : Fin (2 ^ width)) : Fin (2 ^ width) :=
  if hvalid : input.val < modulus.val then
    ⟨(input.val + constant.val) % modulus.val, by
      have hpositive : 0 < modulus.val := by omega
      exact lt_of_lt_of_le (Nat.mod_lt _ hpositive) (by have := modulus.isLt; omega)⟩
  else input

/-- First reflection pivot in the three-reflection offset construction. -/
def offsetFirstPivot {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) : Fin (2 ^ width + 1) :=
  ⟨modulus.val - constant.val, by have := modulus.isLt; omega⟩

/-- Final reflection pivot in the three-reflection offset construction. -/
def offsetLastPivot {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) : Fin (2 ^ width + 1) :=
  ⟨constant.val, by have := constant.isLt; have := modulus.isLt; omega⟩

lemma gidneyModularWord_val {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (input : Fin (2 ^ width)) :
    (modularWordOutput modulus constant input).val =
      if input.val < modulus.val then (input.val + constant.val) % modulus.val else input.val := by
  unfold modularWordOutput
  split_ifs <;> rfl

/-- Three finite reflections equal the independently specified modular output on every label. -/
lemma gidneyModularWord_three_pivots {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (input : Fin (2 ^ width)) :
    pivotWordOutput (offsetLastPivot modulus constant)
        (pivotWordOutput modulus (pivotWordOutput (offsetFirstPivot modulus constant) input)) =
      modularWordOutput modulus constant input := by
  apply Fin.ext
  change pivotFlip constant.val
      (pivotFlip modulus.val
        (pivotFlip (modulus.val - constant.val) input.val)) = _
  rw [gidneyModularWord_val]
  exact pivotFlip_three_eq_modular_offset (by have := constant.isLt; omega)

/-- The original canonical input domain receives ordinary modular addition. -/
lemma gidneyModularWord_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (input : Fin (2 ^ width))
    (hvalid : input.val < modulus.val) :
    (modularWordOutput modulus constant input).val =
      (input.val + constant.val) % modulus.val := by
  rw [gidneyModularWord_val, if_pos hvalid]

/-- Every label outside the residue range is individually fixed. -/
lemma gidneyModularWord_outside {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (input : Fin (2 ^ width))
    (houtside : modulus.val ≤ input.val) :
    modularWordOutput modulus constant input = input := by
  unfold modularWordOutput
  rw [dif_neg (by omega : ¬input.val < modulus.val)]

/-- Zero constant is included without a nonzero-coefficient hypothesis. -/
lemma gidneyModularWord_zero {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (hzero : constant.val = 0)
    (input : Fin (2 ^ width)) : modularWordOutput modulus constant input = input := by
  apply Fin.ext
  rw [gidneyModularWord_val]
  by_cases hvalid : input.val < modulus.val
  · simpa only [if_pos hvalid, hzero, Nat.add_zero] using Nat.mod_eq_of_lt hvalid
  · rw [if_neg hvalid]

/-- Modulus one fixes its unique valid residue and all remaining binary labels. -/
lemma gidneyModularWord_modulus_one {width : Nat} (modulus : Fin (2 ^ width + 1))
    (hone : modulus.val = 1) (constant : Fin (modulus.val + 1))
    (input : Fin (2 ^ width)) : modularWordOutput modulus constant input = input := by
  apply Fin.ext
  rw [gidneyModularWord_val]
  by_cases hvalid : input.val < modulus.val
  · rw [if_pos hvalid]
    have hzero : input.val = 0 := by omega
    simpa only [hone, Nat.mod_one] using hzero.symm
  · rw [if_neg hvalid]


end QuantumAlg.Nat.FixedWidth
