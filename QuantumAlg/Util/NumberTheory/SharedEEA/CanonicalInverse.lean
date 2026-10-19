/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.InverseOutput

/-!
# Canonical modular meaning of the source's corrected inverse

The signed terminal EEA output is the canonical representative of the
inverse in `ZMod`, on the coprime positive-residue domain
[LYL+26, sec_EEA/sub_4phase.tex:123-125]. Its strict residue bound is derived
from the conserved modulus and proved inverse product, rather than added
as a caller condition. The independently defined canonical value uses
only the mathematical residue inverse and no EEA iteration or native code.
The coprime domain is a project proof extension of the source's prime domain.
Unit inputs modulo one remain in the canonical mathematical specification;
their execution requires a separate branch from the positive-residue EEA.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.CanonicalInverse

noncomputable section

/-- The canonical mathematical residue inverse in the original input width. -/
def word (modulus : Nat) (modulusPositive : 0 < modulus) (input : Nat) :
    Fin (2 ^ modulus.size) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  exact ⟨((input : ZMod modulus)⁻¹).val,
    (ZMod.val_lt ((input : ZMod modulus)⁻¹)).trans (Nat.lt_size_self modulus)⟩

/-- The canonical inverse word is zero modulo one, including its unique unit input. -/
lemma word_one (input : Nat) : word 1 (by decide) input = 0 := by
  apply Fin.ext
  have bound := ZMod.val_lt ((input : ZMod 1)⁻¹)
  change ((input : ZMod 1)⁻¹).val = 0
  omega

/-- Original units internally supply the nontrivial EEA branch's value and width conditions. -/
lemma unit_input_conditions (modulus : Nat) (nontrivial : 1 < modulus)
    (input : (ZMod modulus)ˣ) :
    0 < (input : ZMod modulus).val ∧ (input : ZMod modulus).val < modulus ∧
      Nat.Coprime (input : ZMod modulus).val modulus ∧ 2 ≤ modulus.size.size := by
  let : NeZero modulus := ⟨by omega⟩
  have coprime := ZMod.val_coe_unit_coprime input
  have positive : 0 < (input : ZMod modulus).val := by
    by_contra notPositive
    have zero : (input : ZMod modulus).val = 0 := by omega
    rw [zero, Nat.coprime_zero_left] at coprime
    omega
  have modulusWidth : 1 < modulus.size := Nat.lt_size.mpr nontrivial
  have lengthWidth : 1 < modulus.size.size := Nat.lt_size.mpr modulusWidth
  exact ⟨positive, ZMod.val_lt _, coprime, lengthWidth⟩

/-- The terminal corrected coefficient is at most the original conserved modulus. -/
lemma source_le (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (InverseOutput.word modulus input positive bounded).val ≤ modulus := by
  have coefficient := (Capacity.iteration_fields_le _ modulus
    (TerminalPadding.final_admissible modulus input positive bounded)
    (TerminalPadding.final_balance modulus input)).2.2.2
  change SignedInvariant.output modulus (TerminalPadding.finalState modulus input)
    (SignedTrajectory.finalIteration modulus input) ≤ modulus
  unfold SignedInvariant.output
  split
  · exact coefficient
  · exact Nat.sub_le _ _

/-- A coprime positive residue excludes the noncanonical endpoint without an extra fit condition. -/
lemma source_lt (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (InverseOutput.word modulus input positive bounded).val < modulus := by
  let : Fact (1 < modulus) := ⟨by omega⟩
  have bound := source_le modulus input positive bounded
  have product := InverseOutput.word_product modulus input coprime positive bounded
  by_contra notLess
  have same : (InverseOutput.word modulus input positive bounded).val = modulus := by omega
  rw [same, ZMod.natCast_self, mul_zero] at product
  exact zero_ne_one product

/-- The complete source mathematics gives the independently specified canonical residue inverse. -/
lemma source_eq_word (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    InverseOutput.word modulus input positive bounded =
      word modulus (positive.trans bounded) input := by
  let : NeZero modulus := ⟨Nat.ne_of_gt (positive.trans bounded)⟩
  have unit : IsUnit (input : ZMod modulus) :=
    (ZMod.isUnit_iff_coprime input modulus).2 coprime
  have inverseLaw : (input : ZMod modulus) * (input : ZMod modulus)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one input coprime
  have same : ((InverseOutput.word modulus input positive bounded).val : ZMod modulus) =
      (input : ZMod modulus)⁻¹ :=
    unit.mul_left_cancel
      ((InverseOutput.word_product modulus input coprime positive bounded).trans inverseLaw.symm)
  have values := congrArg ZMod.val same
  rw [ZMod.val_natCast,
    Nat.mod_eq_of_lt (source_lt modulus input coprime positive bounded)] at values
  exact Fin.ext values

end

end QuantumAlg.NumberTheory.SharedEEA.CanonicalInverse
