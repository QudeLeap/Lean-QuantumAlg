/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Defs
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Equiv
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
import Mathlib.Data.Nat.Bitwise

/-!
# Independent reversible modular-power XOR arithmetic

The full finite permutation computes selected unit powers, XORs the current
power into an arbitrary target, and applies the mathematical inverse of the
same computation. Every compute word is restored on every finite label.
The canonical initial power is one modulo the modulus and the auxiliary is
zero; on this subspace the target receives the modular power. These are pure
arithmetic statements, independent of gates, storage, and resource budgets
[VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.Nat.FixedWidth

noncomputable section

open QuantumAlg.Nat.FixedWidth.UnitExponentiation

/-- Preserve every compute word and XOR its current power into the independent target. -/
public def unitPowerCopyOutput {exponentWidth width : Nat}
    (state : (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width)) :
    (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width) :=
  (state.1, ⟨state.2.val ^^^ state.1.2.1.val,
    Nat.xor_lt_two_pow state.2.isLt state.1.2.1.isLt⟩)

lemma unitPowerCopyOutput_involutive (exponentWidth width : Nat) :
    Function.Involutive
      (unitPowerCopyOutput (exponentWidth := exponentWidth) (width := width)) := by
  intro state
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change ((state.2.val ^^^ state.1.2.1.val) ^^^ state.1.2.1.val) = state.2.val
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The full finite XOR copy is its own mathematical inverse. -/
def unitPowerCopyEquiv (exponentWidth width : Nat) :
    Equiv.Perm ((Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) ×
      Fin (2 ^ width)) where
  toFun := unitPowerCopyOutput
  invFun := unitPowerCopyOutput
  left_inv := unitPowerCopyOutput_involutive exponentWidth width
  right_inv := unitPowerCopyOutput_involutive exponentWidth width

/-- The independent finite compute equivalence preserves the separate target word. -/
public def unitPowerForwardEquiv (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    Equiv.Perm ((Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) ×
      Fin (2 ^ width)) :=
  Equiv.prodCongr (unitPowerBitsEquiv modulus base (List.ofFn fun bit => bit)) (Equiv.refl _)

/-- Independent total arithmetic action of compute, XOR copy, and mathematical inverse. -/
public def unitPowerOracleOutput {exponentWidth width : Nat} (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ)
    (state : (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width)) :
    (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width) :=
  (unitPowerForwardEquiv exponentWidth width modulus base).symm
    (unitPowerCopyOutput (unitPowerForwardEquiv exponentWidth width modulus base state))

/-- The total modular-power XOR action is an independently constructed finite equivalence. -/
def unitPowerOracleEquiv (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    Equiv.Perm ((Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) ×
      Fin (2 ^ width)) :=
  (unitPowerForwardEquiv exponentWidth width modulus base).trans
    (unitPowerCopyEquiv exponentWidth width) |>.trans
      (unitPowerForwardEquiv exponentWidth width modulus base).symm

lemma unitPowerOracleEquiv_apply (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (state : (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width)) :
    unitPowerOracleEquiv exponentWidth width modulus base state =
      unitPowerOracleOutput modulus base state := rfl

/-- Uncomputation returns all three compute fields, even for arbitrary initial work words. -/
lemma unitPowerOracleOutput_compute {exponentWidth width : Nat}
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (state : (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width)) :
    (unitPowerOracleOutput modulus base state).1 = state.1 := by
  change (unitPowerBitsEquiv modulus base (List.ofFn fun bit : Fin exponentWidth => bit)).symm
    (unitPowerBitsEquiv modulus base (List.ofFn fun bit : Fin exponentWidth => bit) state.1) = _
  exact Equiv.symm_apply_apply _ _

private lemma selected_unit_word {exponentWidth width : Nat}
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base seed : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (exponent : Fin (2 ^ exponentWidth)) :
    unitPowerStageEquiv modulus base bit (exponent, unitResidueWord modulus positive seed, 0) =
      (exponent, unitResidueWord modulus positive (selectedUnit base exponent.val bit * seed),
        0) := by
  rw [unitPowerStageEquiv_apply]
  cases selected : exponent.val.testBit bit.val
  · simp only [selectedUnit, selected, Bool.false_eq_true, if_false, one_mul]
  · simp only [selectedUnit, selected, if_true,
      unitMultiplicationPairEquiv_clean modulus positive _ _
        (unitResidueWord_valid modulus positive seed), unitProductWord_unitResidueWord]

/-- Pure selected-power arithmetic returns the zero auxiliary at each static stage boundary. -/
lemma unitPowerBitsEquiv_unit_word {exponentWidth width : Nat}
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (bits : List (Fin exponentWidth))
    (exponent : Fin (2 ^ exponentWidth)) (seed : (ZMod modulus.val)ˣ) :
    unitPowerBitsEquiv modulus base bits (exponent, unitResidueWord modulus positive seed, 0) =
      (exponent, unitResidueWord modulus positive
        (scheduledUnit base exponent.val bits * seed), 0) := by
  induction bits generalizing seed with
  | nil => simp only [unitPowerBitsEquiv, Equiv.refl_apply, scheduledUnit, List.map_nil,
      List.prod_nil, one_mul]
  | cons bit bits ih =>
      change unitPowerBitsEquiv modulus base bits
        (unitPowerStageEquiv modulus base bit
          (exponent, unitResidueWord modulus positive seed, 0)) = _
      rw [selected_unit_word modulus positive base seed bit exponent, ih]
      have sameUnit : scheduledUnit base exponent.val bits *
          (selectedUnit base exponent.val bit * seed) =
            scheduledUnit base exponent.val (bit :: bits) * seed := by
        simp only [scheduledUnit, List.map_cons, List.prod_cons]
        ac_rfl
      exact congrArg (fun unit : (ZMod modulus.val)ˣ =>
        (exponent, unitResidueWord modulus positive unit, (0 : Fin (2 ^ width)))) sameUnit

/-- Canonical initialization computes the modular power without a parity restriction. -/
lemma unitPowerForwardEquiv_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (target : Fin (2 ^ width)) :
    unitPowerForwardEquiv exponentWidth width modulus base
        ((exponent, unitResidueWord modulus positive 1, 0), target) =
      ((exponent, unitResidueWord modulus positive (base ^ exponent.val), 0), target) := by
  apply Prod.ext
  · change unitPowerBitsEquiv modulus base (List.ofFn fun bit : Fin exponentWidth => bit)
      (exponent, unitResidueWord modulus positive 1, 0) = _
    rw [unitPowerBitsEquiv_unit_word, scheduledUnit_all_eq_pow, mul_one]
  · rfl

/-- The arbitrary target receives the modular power and both prepared words return exactly. -/
lemma unitPowerOracleOutput_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (target : Fin (2 ^ width)) :
    unitPowerOracleOutput modulus base ((exponent, unitResidueWord modulus positive 1, 0), target) =
      ((exponent, unitResidueWord modulus positive 1, 0),
        ⟨target.val ^^^ (unitResidueWord modulus positive (base ^ exponent.val)).val,
          Nat.xor_lt_two_pow target.isLt
            (unitResidueWord modulus positive (base ^ exponent.val)).isLt⟩) := by
  unfold unitPowerOracleOutput
  apply (unitPowerForwardEquiv exponentWidth width modulus base).injective
  rw [Equiv.apply_symm_apply, unitPowerForwardEquiv_clean, unitPowerForwardEquiv_clean]
  rfl

end

end QuantumAlg.Nat.FixedWidth
