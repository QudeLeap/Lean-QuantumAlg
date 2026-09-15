/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Word
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-!
# Finite-word accumulation of precomputed modular constants

Each selected stage applies the total finite modular offset, which fixes
noncanonical labels. The compiled residue is `a * 2^i mod N`, so no
doubling permutation, parity condition, or inverse coefficient is needed.
The full-width result reuses the binary-prefix arithmetic recurrence.
-/

namespace QuantumAlg.Nat.FixedWidth

open QuantumAlg.Nat.FixedWidth.ModularAccumulate

/-- The fitted compile-time residue; the unused zero-modulus extension selects zero. -/
def accumulateConstant {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient index : Nat) : Fin (modulus.val + 1) :=
  if positive : 0 < modulus.val then
    ⟨stageConstantResidue modulus.val coefficient index,
      Nat.lt_trans (stageConstantResidue_lt positive) (Nat.lt_succ_self _)⟩
  else 0

theorem accumulateConstant_val {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient index : Nat) (positive : 0 < modulus.val) :
    (accumulateConstant modulus coefficient index).val =
      stageConstantResidue modulus.val coefficient index := by
  simp only [accumulateConstant, dif_pos positive]

/-- A source bit selects one total modular offset; the source itself is external to this action. -/
def selectedWordOffset {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source : Fin (2 ^ width)) (index : Nat)
    (target : Fin (2 ^ width)) : Fin (2 ^ width) :=
  if source.val.testBit index then
    modularWordOutput modulus (accumulateConstant modulus coefficient index) target
  else target

/-- Scan source bits in increasing little-endian order. -/
public def accumulateWordPrefix {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width)) : Nat → Fin (2 ^ width)
  | 0 => target
  | index + 1 => selectedWordOffset modulus coefficient source index
      (accumulateWordPrefix modulus coefficient source target index)

/-- Every canonical accumulator prefix remains canonical. -/
theorem accumulateWordPrefix_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width))
    (valid : target.val < modulus.val) (count : Nat) :
    (accumulateWordPrefix modulus coefficient source target count).val < modulus.val := by
  induction count with
  | zero => exact valid
  | succ index ih =>
      change (selectedWordOffset modulus coefficient source index
        (accumulateWordPrefix modulus coefficient source target index)).val < modulus.val
      unfold selectedWordOffset
      split_ifs
      · rw [gidneyModularWord_valid modulus _ _ ih]
        exact Nat.mod_lt _ (by omega)
      · exact ih

/-- The finite recurrence agrees with the existing independent natural-number prefix. -/
theorem accumulateWordPrefix_val {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width))
    (valid : target.val < modulus.val) (count : Nat) :
    (accumulateWordPrefix modulus coefficient source target count).val =
      accumulateSelected modulus.val coefficient source.val target.val count := by
  have positive : 0 < modulus.val := by omega
  induction count with
  | zero => exact (Nat.mod_eq_of_lt valid).symm
  | succ index ih =>
      have hprefix := accumulateWordPrefix_valid modulus coefficient source target valid index
      change (selectedWordOffset modulus coefficient source index
        (accumulateWordPrefix modulus coefficient source target index)).val = _
      rw [accumulateSelected_succ, selectedBitContribution_eq_if]
      by_cases selected : source.val.testBit index = true
      · rw [selectedWordOffset, if_pos selected, if_pos selected,
          gidneyModularWord_valid modulus _ _ hprefix,
          accumulateConstant_val modulus coefficient index positive, ih]
      · rw [selectedWordOffset, if_neg selected, if_neg selected, Nat.add_zero]
        rw [← ih, Nat.mod_eq_of_lt hprefix]

/-- Full-width multiplication-accumulation for arbitrary coefficients and positive moduli. -/
theorem accumulateWordPrefix_full {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width))
    (valid : target.val < modulus.val) :
    (accumulateWordPrefix modulus coefficient source target width).val =
      (target.val + coefficient * source.val) % modulus.val := by
  rw [accumulateWordPrefix_val modulus coefficient source target valid]
  exact accumulateSelected_eq_add_mul_mod_of_lt_two_pow source.isLt

/-- The total extension fixes noncanonical labels at every prefix, independently of source bits. -/
theorem accumulateWordPrefix_outside {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width))
    (outside : modulus.val ≤ target.val) (count : Nat) :
    accumulateWordPrefix modulus coefficient source target count = target := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change selectedWordOffset modulus coefficient source index
        (accumulateWordPrefix modulus coefficient source target index) = target
      rw [ih]
      unfold selectedWordOffset
      split_ifs
      · exact gidneyModularWord_outside modulus _ target outside
      · rfl

end QuantumAlg.Nat.FixedWidth
