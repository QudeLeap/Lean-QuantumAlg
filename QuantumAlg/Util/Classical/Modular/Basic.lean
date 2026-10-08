/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.ModEq
public import QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.Classical.Arithmetic

/-!
# Canonical fixed-width modular values

This module defines a proved modulus specification and the intrinsic carrier for
canonical residues.  A residue is a `Fin` value below the specified modulus;
the storage width is retained by the index of `ModulusSpec`.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace Modular

/-- A positive nontrivial modulus that fits in one declared word width. -/
public structure ModulusSpec (width : Nat) where
  /-- The mathematical modulus. -/
  modulus : Nat
  /-- Modular arithmetic in this layer excludes the trivial moduli zero and one. -/
  two_le : 2 ≤ modulus
  /-- Every canonical representative fits in the declared storage width. -/
  le_capacity : modulus ≤ ClassicalAlgorithms.modulus width

theorem modulusSpec_modulus_pos {width : Nat} (spec : ModulusSpec width) :
    0 < spec.modulus := by
  have modulusTwo := spec.two_le
  omega

theorem modulusSpec_one_lt {width : Nat} (spec : ModulusSpec width) :
    1 < spec.modulus := by
  have modulusTwo := spec.two_le
  omega

/-- A nontrivial fitted modulus requires a nonempty storage width. -/
theorem modulusSpec_width_pos {width : Nat} (spec : ModulusSpec width) :
    0 < width := by
  by_contra widthNotPositive
  have widthZero : width = 0 := Nat.eq_zero_of_not_pos widthNotPositive
  subst width
  have modulusLeOne : spec.modulus ≤ 1 := by
    simpa [ClassicalAlgorithms.modulus] using spec.le_capacity
  have modulusTwo := spec.two_le
  omega

/-- One additional bit can represent the modulus itself, including at capacity. -/
theorem modulusSpec_modulus_lt_extended {width : Nat} (spec : ModulusSpec width) :
    spec.modulus < ClassicalAlgorithms.modulus (width + 1) := by
  have capacityPositive := ClassicalAlgorithms.fixedWidthModulus_pos width
  have modulusBound := spec.le_capacity
  simp only [ClassicalAlgorithms.modulus, pow_succ] at capacityPositive modulusBound ⊢
  omega

/-- The modulus represented exactly in one additional bit. -/
def ModulusSpec.extendedWord {width : Nat} (spec : ModulusSpec width) :
    Word (width + 1) :=
  ⟨spec.modulus, modulusSpec_modulus_lt_extended spec⟩

@[simp] theorem modulusSpec_extendedWord_val {width : Nat}
    (spec : ModulusSpec width) :
    spec.extendedWord.val = spec.modulus :=
  rfl

/-- Every positive width can store the smallest admitted modulus. -/
theorem fixedWidth_two_le_modulus_of_pos {width : Nat} (widthPositive : 0 < width) :
    2 ≤ ClassicalAlgorithms.modulus width := by
  cases width with
  | zero => simp at widthPositive
  | succ width =>
      have capacityPositive := Nat.two_pow_pos width
      simp only [ClassicalAlgorithms.modulus, pow_succ]
      omega

/-- The smallest admitted modulus at any positive width. -/
def ModulusSpec.minimum (width : Nat) (widthPositive : 0 < width) :
    ModulusSpec width where
  modulus := 2
  two_le := le_rfl
  le_capacity := fixedWidth_two_le_modulus_of_pos widthPositive

@[simp] theorem modulusSpec_minimum_modulus (width : Nat)
    (widthPositive : 0 < width) :
    (ModulusSpec.minimum width widthPositive).modulus = 2 :=
  rfl

/-- The largest admitted modulus at any positive width. -/
def ModulusSpec.maximum (width : Nat) (widthPositive : 0 < width) :
    ModulusSpec width where
  modulus := ClassicalAlgorithms.modulus width
  two_le := fixedWidth_two_le_modulus_of_pos widthPositive
  le_capacity := le_rfl

@[simp] theorem modulusSpec_maximum_modulus (width : Nat)
    (widthPositive : 0 < width) :
    (ModulusSpec.maximum width widthPositive).modulus = ClassicalAlgorithms.modulus width :=
  rfl

/-- An intrinsically canonical representative for one proved modulus. -/
public abbrev Residue {width : Nat} (spec : ModulusSpec width) := Fin spec.modulus

namespace Residue

/-- Reduce a natural number to its canonical representative. -/
def ofNat {width : Nat} (spec : ModulusSpec width) (value : Nat) : Residue spec :=
  ⟨value % spec.modulus, Nat.mod_lt value (modulusSpec_modulus_pos spec)⟩

@[simp] theorem residueOfNat_val {width : Nat} (spec : ModulusSpec width)
    (value : Nat) :
    (ofNat spec value).val = value % spec.modulus :=
  rfl

theorem residue_val_lt_modulus {width : Nat} {spec : ModulusSpec width}
    (value : Residue spec) :
    value.val < spec.modulus :=
  value.isLt

/-- Store a canonical residue in its declared fixed width without reduction. -/
def toWord {width : Nat} {spec : ModulusSpec width} (value : Residue spec) :
    Word width :=
  ⟨value.val, value.isLt.trans_le spec.le_capacity⟩

@[simp] theorem residueToWord_val {width : Nat} {spec : ModulusSpec width}
    (value : Residue spec) :
    value.toWord.val = value.val :=
  rfl

theorem residueOfNat_val_of_lt {width : Nat} (spec : ModulusSpec width)
    (value : Nat) (valueRange : value < spec.modulus) :
    (ofNat spec value).val = value := by
  exact Nat.mod_eq_of_lt valueRange

/-- Reducing an already canonical representative changes nothing. -/
@[simp] theorem residueOfNat_idem {width : Nat} {spec : ModulusSpec width}
    (value : Residue spec) :
    ofNat spec value.val = value := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.isLt

/-- Canonical reduction preserves the represented congruence class. -/
theorem residueOfNat_modEq {width : Nat} (spec : ModulusSpec width)
    (value : Nat) :
    (ofNat spec value).val ≡ value [MOD spec.modulus] := by
  change value % spec.modulus ≡ value [MOD spec.modulus]
  exact Nat.mod_modEq value spec.modulus

/-- Congruent naturals have the same canonical representative. -/
theorem residueOfNat_eq_of_modEq {width : Nat} (spec : ModulusSpec width)
    {left right : Nat} (equivalent : left ≡ right [MOD spec.modulus]) :
    ofNat spec left = ofNat spec right := by
  apply Fin.ext
  exact equivalent

/-- Canonical zero. -/
def zero {width : Nat} (spec : ModulusSpec width) : Residue spec :=
  ofNat spec 0

/-- Canonical one. -/
def one {width : Nat} (spec : ModulusSpec width) : Residue spec :=
  ofNat spec 1

@[simp] theorem residueZero_val {width : Nat} (spec : ModulusSpec width) :
    (zero spec).val = 0 := by
  simp [zero]

@[simp] theorem residueOne_val {width : Nat} (spec : ModulusSpec width) :
    (one spec).val = 1 := by
  exact Nat.mod_eq_of_lt (modulusSpec_one_lt spec)

end Residue

/-- At the maximum admitted modulus, every word is already canonical. -/
theorem fixedWidthWord_lt_specModulus_of_eq_capacity {width : Nat}
    (spec : ModulusSpec width)
    (maximum : spec.modulus = ClassicalAlgorithms.modulus width)
    (word : Word width) :
    word.val < spec.modulus := by
  rw [maximum]
  exact ClassicalAlgorithms.fixedWidthWord_lt_modulus word

end Modular

end ClassicalAlgorithms
end QuantumAlg

end
