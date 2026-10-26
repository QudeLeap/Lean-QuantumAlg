/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Invariant
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Constants
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate
import Mathlib.Data.ZMod.Basic

/-!
# Binary-weight arithmetic of the actual forward and explicit inverse MAC

The independently specified selected-offset recurrence reconstructs the
ordinary modular product. The separately emitted negative residues equal
the positive weights of the negative coefficient modulo the same modulus;
this is a static arithmetic identity, with no reversal of an instrument
[VBE95, 9511018.tex:333-367; G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- A zero global control skips every independently specified modular offset. -/
lemma selectedPrefixValue_disabled (modulus : BitVec width)
    (constants : Fin width → BitVec width) (source : BitVec width) (initial count : Nat)
    (bounded : count ≤ width) :
    selectedPrefixValue modulus constants source false initial count bounded = initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [selectedPrefixValue, Bool.false_and, Bool.false_eq_true, if_false] using
        ih (by omega)

/-- Forward static weights give the original independent binary modular-accumulation recurrence. -/
lemma selectedPrefixValue_forward (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient : Nat) (source : BitVec width) (initial : Nat)
    (canonical : initial < modulus.toNat) (count : Nat) (bounded : count ≤ width) :
    selectedPrefixValue modulus (forwardConstant modulus coefficient) source true initial
        count bounded =
      Nat.FixedWidth.ModularAccumulate.accumulateSelected modulus.toNat coefficient
        source.toNat initial count := by
  induction count with
  | zero => exact (Nat.mod_eq_of_lt canonical).symm
  | succ count ih =>
      rw [selectedPrefixValue, Nat.FixedWidth.ModularAccumulate.accumulateSelected_succ,
        Nat.FixedWidth.ModularAccumulate.selectedBitContribution_eq_if,
        forwardConstant_nat modulus coefficient _ positive, ih (by omega)]
      cases source.toNat.testBit count
      · simp only [Bool.true_and, Bool.false_eq_true, if_false, Nat.add_zero,
          Nat.mod_eq_of_lt (Nat.FixedWidth.ModularAccumulate.accumulateSelected_lt positive)]
      · simp only [Bool.true_and, if_true]

private lemma negative_weight (modulus coefficient index : Nat) (positive : 0 < modulus) :
    (modulus - Nat.FixedWidth.ModularAccumulate.stageConstantResidue
      modulus coefficient index) % modulus =
      Nat.FixedWidth.ModularAccumulate.stageConstantResidue
        modulus (modulus - coefficient % modulus) index := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ modulus).mp
  rw [Nat.cast_sub (Nat.le_of_lt
      (Nat.FixedWidth.ModularAccumulate.stageConstantResidue_lt positive)),
    Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt coefficient positive))]
  simp only [Nat.FixedWidth.ModularAccumulate.stageConstantResidue, ZMod.natCast_mod,
    Nat.cast_mul, ZMod.natCast_self, zero_sub]
  ring

/-- Each explicit negative row has exactly the canonical weight of the negative coefficient. -/
lemma inverseConstant_eq_forward_negative (modulus : BitVec width) (coefficient : Nat)
    (positive : 0 < modulus.toNat) (index : Fin width) :
    inverseConstant modulus coefficient index =
      forwardConstant modulus (modulus.toNat - coefficient % modulus.toNat) index := by
  apply BitVec.eq_of_toNat_eq
  rw [inverseConstant_nat modulus coefficient index positive,
    forwardConstant_nat modulus _ index positive]
  exact negative_weight modulus.toNat coefficient index.val positive

/-- The complete actual forward MAC adds the independently specified product modulo the modulus. -/
lemma forwardMACWord_target_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat) (coefficient : Nat)
    (initial : Data) (ready : layout.Ready modulus initial) :
    (layout.targetWord (wordLabel (layout.forwardMACWord wide modulus coefficient) initial)).toNat =
      if layout.control.get initial then
        ((layout.targetWord initial).toNat + coefficient * (layout.sourceWord initial).toNat) %
          modulus.toNat else (layout.targetWord initial).toNat := by
  rw [forwardMACWord, accumulateWord, accumulatePrefixWord_target_nat layout wide modulus _
    (fun index => forwardConstant_canonical modulus coefficient index positive)
      width le_rfl initial ready]
  cases enabled : layout.control.get initial
  · exact selectedPrefixValue_disabled modulus _ _ _ width le_rfl
  · rw [selectedPrefixValue_forward modulus positive coefficient _ _ ready.canonical,
      Nat.FixedWidth.ModularAccumulate.accumulateSelected_eq_add_mul_mod_of_lt_two_pow
        (layout.sourceWord initial).isLt]
    rfl

/-- The explicit negative-residue MAC subtracts its product by actual modular additions. -/
lemma inverseMACWord_target_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat) (coefficient : Nat)
    (initial : Data) (ready : layout.Ready modulus initial) :
    (layout.targetWord (wordLabel (layout.inverseMACWord wide modulus coefficient) initial)).toNat =
      if layout.control.get initial then
        ((layout.targetWord initial).toNat + (modulus.toNat - coefficient % modulus.toNat) *
          (layout.sourceWord initial).toNat) % modulus.toNat else
            (layout.targetWord initial).toNat := by
  have sameConstants : inverseConstant modulus coefficient =
      forwardConstant modulus (modulus.toNat - coefficient % modulus.toNat) := by
    funext index
    exact inverseConstant_eq_forward_negative modulus coefficient positive index
  change (layout.targetWord
    (wordLabel (layout.accumulateWord wide modulus (inverseConstant modulus coefficient))
      initial)).toNat = _
  rw [sameConstants]
  exact forwardMACWord_target_nat layout wide modulus positive _ initial ready

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
