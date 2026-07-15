/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularInversion.Basic
public import QuantumAlg.Primitives.MAU.CleanInterface

/-!
# Reversible modular division basics

This module records the unit-denominator modular-division data registers
and the reversible target-update permutation over `ZMod N` units.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularDivision

/-- The residue quotient `v*u⁻¹` for a unit denominator modulo `N`. -/
def quotientResidue {N : ℕ} (u : (ZMod N)ˣ) (v : ZMod N) : ZMod N :=
  v * ModularInversion.inverseResidue u

/-- Data registers for the unit-denominator modular division map. The clean
flag represents temporary work after uncomputation. -/
structure Data (N : ℕ) where
  /-- Unit denominator used for the division. -/
  denominator : (ZMod N)ˣ
  /-- Numerator residue being multiplied by the inverse denominator. -/
  numerator : ZMod N
  /-- Target register receiving the quotient residue. -/
  target : ZMod N
  /-- Temporary cleanup flag carried by the endpoint. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (N : ℕ) [NeZero N] : Fintype (Data N) := by
  classical
  let e : Data N ≃ ((ZMod N)ˣ × ZMod N × ZMod N × Bool) := {
    toFun := fun x => (x.denominator, (x.numerator, (x.target, x.flag)))
    invFun := fun x =>
      { denominator := x.1, numerator := x.2.1, target := x.2.2.1, flag := x.2.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨denominator, rest⟩
      rcases rest with ⟨numerator, rest'⟩
      rcases rest' with ⟨target, flag⟩
      rfl
  }
  exact Fintype.ofEquiv ((ZMod N)ˣ × ZMod N × ZMod N × Bool) e.symm

namespace Data

/-- The clean temporary-flag convention for modular division. -/
def FlagClean {N : ℕ} (x : Data N) : Prop :=
  x.flag = false

/-- Add `v*u⁻¹` into the target register, preserving the denominator, numerator,
and flag. -/
def addQuotientIntoTarget {N : ℕ} (x : Data N) : Data N where
  denominator := x.denominator
  numerator := x.numerator
  target := x.target + quotientResidue x.denominator x.numerator
  flag := x.flag

/-- Subtract `v*u⁻¹` from the target register, preserving the denominator,
numerator, and flag. -/
def subQuotientFromTarget {N : ℕ} (x : Data N) : Data N where
  denominator := x.denominator
  numerator := x.numerator
  target := x.target - quotientResidue x.denominator x.numerator
  flag := x.flag

@[simp] theorem addQuotientIntoTarget_denominator {N : ℕ} (x : Data N) :
    x.addQuotientIntoTarget.denominator = x.denominator :=
  rfl

@[simp] theorem addQuotientIntoTarget_numerator {N : ℕ} (x : Data N) :
    x.addQuotientIntoTarget.numerator = x.numerator :=
  rfl

@[simp] theorem addQuotientIntoTarget_target {N : ℕ} (x : Data N) :
    x.addQuotientIntoTarget.target =
      x.target + quotientResidue x.denominator x.numerator :=
  rfl

@[simp] theorem addQuotientIntoTarget_flag {N : ℕ} (x : Data N) :
    x.addQuotientIntoTarget.flag = x.flag :=
  rfl

@[simp] theorem subQuotientFromTarget_denominator {N : ℕ} (x : Data N) :
    x.subQuotientFromTarget.denominator = x.denominator :=
  rfl

@[simp] theorem subQuotientFromTarget_numerator {N : ℕ} (x : Data N) :
    x.subQuotientFromTarget.numerator = x.numerator :=
  rfl

@[simp] theorem subQuotientFromTarget_target {N : ℕ} (x : Data N) :
    x.subQuotientFromTarget.target =
      x.target - quotientResidue x.denominator x.numerator :=
  rfl

@[simp] theorem subQuotientFromTarget_flag {N : ℕ} (x : Data N) :
    x.subQuotientFromTarget.flag = x.flag :=
  rfl

/-- Clean temporary flags remain clean after modular division. -/
theorem addQuotientIntoTarget_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.addQuotientIntoTarget.FlagClean :=
  h

/-- Clean temporary flags remain clean after inverse modular division. -/
theorem subQuotientFromTarget_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.subQuotientFromTarget.FlagClean :=
  h

/-- Unit-denominator modular division as a reversible permutation. -/
def divEquiv (N : ℕ) : Equiv.Perm (Data N) where
  toFun := addQuotientIntoTarget
  invFun := subQuotientFromTarget
  left_inv := by
    intro x
    cases x
    simp [addQuotientIntoTarget, subQuotientFromTarget]
  right_inv := by
    intro x
    cases x
    simp [addQuotientIntoTarget, subQuotientFromTarget]

@[simp] theorem divEquiv_apply {N : ℕ} (x : Data N) :
    divEquiv N x = x.addQuotientIntoTarget :=
  rfl

/-- Modular division with an external work register, leaving the work untouched. -/
def withWorkEquiv (N : ℕ) (Work : Type) : Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr (divEquiv N) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {N : ℕ} {Work : Type} (x : Data N) (w : Work) :
    withWorkEquiv N Work (x, w) = (x.addQuotientIntoTarget, w) :=
  rfl

/-- The division map leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {N : ℕ} {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (withWorkEquiv N Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for unit-denominator modular division. -/
def withWorkCleanMap (N : ℕ) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := withWorkEquiv N Work
  preservesWork := withWorkEquiv_preserves_work

end Data


end ModularDivision
end QuantumAlg
