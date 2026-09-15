/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import all QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.Classical.Modular.Additive
import all QuantumAlg.Util.Classical.NumberTheory.Basic

/-!
# Checked fixed-width modular inversion and division

This module separates partial operations from proof-carrying total operations.
The total inverse on `ZMod` is used only to select a canonical candidate; no
result is exposed unless coprimality proves that the candidate is an inverse.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace NumberTheory

open Modular

/-- A canonical residue accompanied by evidence that it is a unit. -/
structure UnitResidue {width : Nat} (spec : ModulusSpec width) where
  /-- The canonical residue value. -/
  value : Residue spec
  /-- The value is coprime to the modulus, hence invertible. -/
  coprime : Nat.Coprime value.val spec.modulus

@[ext] theorem UnitResidue.ext {width : Nat} {spec : ModulusSpec width}
    {left right : UnitResidue spec} (value : left.value = right.value) :
    left = right := by
  cases left
  cases right
  cases value
  rfl

/-- The canonical representative selected by the extended-GCD inverse on
`ZMod`. This is only a candidate until a coprimality proof is supplied. -/
def inverseCandidate {width : Nat} (spec : ModulusSpec width)
    (value : Residue spec) : Residue spec := by
  letI : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  exact
    ⟨((value.val : ZMod spec.modulus)⁻¹).val,
      ZMod.val_lt ((value.val : ZMod spec.modulus)⁻¹)⟩

@[simp] theorem inverseCandidate_val {width : Nat}
    (spec : ModulusSpec width) (value : Residue spec) :
    (inverseCandidate spec value).val =
      ((value.val : ZMod spec.modulus)⁻¹).val := by
  rfl

/-- A coprime input really multiplies its selected candidate to canonical one. -/
theorem inverseCandidate_mul_mod {width : Nat} (spec : ModulusSpec width)
    (value : Residue spec) (coprime : Nat.Coprime value.val spec.modulus) :
    value.val * (inverseCandidate spec value).val % spec.modulus = 1 := by
  let _ : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  have inverseLaw :
      (value.val : ZMod spec.modulus) *
          (value.val : ZMod spec.modulus)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one value.val coprime
  have valueRange : value.val % spec.modulus = value.val :=
    Nat.mod_eq_of_lt value.isLt
  have modulusNeOne : spec.modulus ≠ 1 :=
    Nat.ne_of_gt (modulusSpec_one_lt spec)
  have valLaw := congrArg ZMod.val inverseLaw
  simpa [ZMod.val_mul, ZMod.val_natCast, valueRange,
    ZMod.val_one'' modulusNeOne] using valLaw

/-- A canonical modular inverse is unique once the denominator is known to be
a unit. This lets expanded Euclidean implementations bridge to the selected
pure candidate without depending on the internal coefficient normalization. -/
theorem inverse_eq_candidate_of_mul_mod {width : Nat}
    (spec : ModulusSpec width) (value inverse : Residue spec)
    (coprime : Nat.Coprime value.val spec.modulus)
    (inverseLaw : value.val * inverse.val % spec.modulus = 1) :
    inverse = inverseCandidate spec value := by
  let _ : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  have oneMod : 1 % spec.modulus = 1 :=
    Nat.mod_eq_of_lt (modulusSpec_one_lt spec)
  have suppliedCast :
      (value.val : ZMod spec.modulus) *
          (inverse.val : ZMod spec.modulus) = 1 := by
    have castNatEq :
        ((value.val * inverse.val : Nat) : ZMod spec.modulus) =
          ((1 : Nat) : ZMod spec.modulus) :=
      (ZMod.natCast_eq_natCast_iff'
        (value.val * inverse.val) 1 spec.modulus).2 (by
          simpa [oneMod] using inverseLaw)
    simpa only [Nat.cast_mul, Nat.cast_one] using castNatEq
  have candidateCast :
      (value.val : ZMod spec.modulus) *
          ((inverseCandidate spec value).val : ZMod spec.modulus) = 1 := by
    have castNatEq :
        ((value.val * (inverseCandidate spec value).val : Nat) :
            ZMod spec.modulus) = ((1 : Nat) : ZMod spec.modulus) :=
      (ZMod.natCast_eq_natCast_iff'
        (value.val * (inverseCandidate spec value).val) 1
          spec.modulus).2 (by
            simpa [oneMod] using
              inverseCandidate_mul_mod spec value coprime)
    simpa only [Nat.cast_mul, Nat.cast_one] using castNatEq
  have valueIsUnit : IsUnit (value.val : ZMod spec.modulus) :=
    (ZMod.isUnit_iff_coprime value.val spec.modulus).2 coprime
  have inverseCast :
      (inverse.val : ZMod spec.modulus) =
        ((inverseCandidate spec value).val : ZMod spec.modulus) :=
    valueIsUnit.mul_left_cancel (suppliedCast.trans candidateCast.symm)
  apply Fin.ext
  have residueModEq :=
    (ZMod.natCast_eq_natCast_iff' inverse.val
      (inverseCandidate spec value).val spec.modulus).1 inverseCast
  rw [Nat.mod_eq_of_lt inverse.isLt,
    Nat.mod_eq_of_lt (inverseCandidate spec value).isLt] at residueModEq
  exact residueModEq

namespace TryInv

/-- A checked inverse accepts one canonical residue. -/
abbrev Input {width : Nat} (spec : ModulusSpec width) := Residue spec

/-- A checked inverse returns a canonical residue exactly on unit inputs. -/
abbrev Output {width : Nat} (spec : ModulusSpec width) := Option (Residue spec)

/-- Public relation for checked inversion. A successful answer may use any
canonical inverse; it is not tied to Mathlib's coefficient normalization. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Output spec) : Prop :=
  match output with
  | none => ¬ Nat.Coprime input.val spec.modulus
  | some inverse =>
      Nat.Coprime input.val spec.modulus ∧
        input.val * inverse.val % spec.modulus = 1

/-- Checked inversion exposes failure instead of treating total ring inverse as
evidence that every residue is a unit. -/
def eval {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : Output spec :=
  if _coprime : Nat.Coprime input.val spec.modulus then
    some (inverseCandidate spec input)
  else
    none

theorem tryInv_eval_eq_none_iff {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = none ↔ ¬ Nat.Coprime input.val spec.modulus := by
  simp [eval]

theorem tryInv_eval_ne_none_iff {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input ≠ none ↔ Nat.Coprime input.val spec.modulus := by
  simp [eval]

theorem tryInv_eval_eq_some_iff {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    (∃ inverse, eval spec input = some inverse) ↔
      Nat.Coprime input.val spec.modulus := by
  simp [eval]

theorem tryInv_eval_some_value {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) (coprime : Nat.Coprime input.val spec.modulus) :
    eval spec input = some (inverseCandidate spec input) := by
  simp [eval, coprime]

theorem tryInv_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : accepts input (eval spec input) := by
  by_cases coprime : Nat.Coprime input.val spec.modulus
  · rw [tryInv_eval_some_value spec input coprime]
    exact ⟨coprime, inverseCandidate_mul_mod spec input coprime⟩
  · rw [(tryInv_eval_eq_none_iff spec input).2 coprime]
    exact coprime

end TryInv

namespace TryDiv

/-- Canonical numerator and denominator for checked division. -/
structure Input {width : Nat} (spec : ModulusSpec width) where
  /-- The numerator. -/
  numerator : Residue spec
  /-- The denominator whose unit status is checked. -/
  denominator : Residue spec
deriving DecidableEq

/-- Checked division has the same optional canonical payload as inversion. -/
abbrev Output {width : Nat} (spec : ModulusSpec width) := Option (Residue spec)

/-- Public relation for checked division. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Output spec) : Prop :=
  match output with
  | none => ¬ Nat.Coprime input.denominator.val spec.modulus
  | some quotient =>
      Nat.Coprime input.denominator.val spec.modulus ∧
        quotient = Modular.Mul.eval spec
          { left := input.numerator,
            right := inverseCandidate spec input.denominator }

/-- Divide by a checked inverse, propagating the nonunit failure exactly. -/
def eval {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : Output spec :=
  match TryInv.eval spec input.denominator with
  | none => none
  | some inverse =>
      some (Modular.Mul.eval spec
        { left := input.numerator, right := inverse })

theorem tryDiv_eval_some_value {width : Nat} (spec : ModulusSpec width)
    (input : Input spec)
    (coprime : Nat.Coprime input.denominator.val spec.modulus) :
    eval spec input = some (Modular.Mul.eval spec
      { left := input.numerator,
        right := inverseCandidate spec input.denominator }) := by
  unfold eval
  rw [TryInv.tryInv_eval_some_value spec input.denominator coprime]

theorem tryDiv_eval_eq_none_iff {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input = none ↔
      ¬ Nat.Coprime input.denominator.val spec.modulus := by
  by_cases coprime : Nat.Coprime input.denominator.val spec.modulus
  · rw [tryDiv_eval_some_value spec input coprime]
    simp [coprime]
  · rw [show eval spec input = none by
      unfold eval
      rw [(TryInv.tryInv_eval_eq_none_iff spec input.denominator).2 coprime]]
    simp [coprime]

theorem tryDiv_eval_ne_none_iff {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) :
    eval spec input ≠ none ↔
      Nat.Coprime input.denominator.val spec.modulus := by
  rw [ne_eq, tryDiv_eval_eq_none_iff]
  simp

theorem tryDiv_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : accepts input (eval spec input) := by
  by_cases coprime : Nat.Coprime input.denominator.val spec.modulus
  · rw [tryDiv_eval_some_value spec input coprime]
    exact ⟨coprime, rfl⟩
  · rw [show eval spec input = none by
      unfold eval
      rw [(TryInv.tryInv_eval_eq_none_iff spec input.denominator).2 coprime]]
    exact coprime

end TryDiv

namespace UnitInv

/-- Proof-carrying unit input for total inversion. -/
abbrev Input {width : Nat} (spec : ModulusSpec width) := UnitResidue spec

/-- Unit inversion always returns a canonical residue. -/
abbrev Output {width : Nat} (spec : ModulusSpec width) := Residue spec

/-- Total unit inversion reuses the same canonical candidate. -/
def eval {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : Output spec :=
  inverseCandidate spec input.value

/-- Mathematical correctness of proof-carrying inversion. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Output spec) : Prop :=
  input.value.val * output.val % spec.modulus = 1

theorem unitInv_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : accepts input (eval spec input) :=
  inverseCandidate_mul_mod spec input.value input.coprime

end UnitInv

namespace UnitDiv

/-- Canonical numerator and proof-carrying unit denominator. -/
structure Input {width : Nat} (spec : ModulusSpec width) where
  /-- The numerator. -/
  numerator : Residue spec
  /-- A denominator carrying the required unit proof. -/
  denominator : UnitResidue spec

/-- Unit division always returns one canonical residue. -/
abbrev Output {width : Nat} (spec : ModulusSpec width) := Residue spec

/-- Divide by the canonical inverse selected for the witnessed denominator. -/
def eval {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : Output spec :=
  Modular.Mul.eval spec
    { left := input.numerator,
      right := UnitInv.eval spec input.denominator }

/-- Mathematical correctness relation for proof-carrying division. -/
def accepts {width : Nat} {spec : ModulusSpec width}
    (input : Input spec) (output : Output spec) : Prop :=
  output = Modular.Mul.eval spec
    { left := input.numerator,
      right := inverseCandidate spec input.denominator.value }

theorem unitDiv_eval_accepts {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : accepts input (eval spec input) :=
  rfl

end UnitDiv

end NumberTheory

end ClassicalAlgorithms
end QuantumAlg

end
