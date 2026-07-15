/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.CleanInterface
public import QuantumAlg.Util.ZModUnits

/-!
# Reversible modular inversion basics

This module records the unit-domain modular-inversion data registers and
the reversible target-update permutation over `ZMod N` units.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularInversion

/-- The residue represented by the inverse of a unit modulo `N`. -/
def inverseResidue {N : ℕ} (u : (ZMod N)ˣ) : ZMod N :=
  ((u⁻¹ : (ZMod N)ˣ) : ZMod N)

/-- Data registers for the unit-domain modular inversion map. The clean flag
represents temporary work after uncomputation. -/
structure Data (N : ℕ) where
  /-- Unit-domain input whose inverse is added into the target. -/
  input : (ZMod N)ˣ
  /-- Target register receiving the inverse residue. -/
  target : ZMod N
  /-- Temporary cleanup flag carried by the endpoint. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (N : ℕ) [NeZero N] : Fintype (Data N) := by
  classical
  let e : Data N ≃ ((ZMod N)ˣ × ZMod N × Bool) := {
    toFun := fun x => (x.input, (x.target, x.flag))
    invFun := fun x => { input := x.1, target := x.2.1, flag := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨input, rest⟩
      rcases rest with ⟨target, flag⟩
      rfl
  }
  exact Fintype.ofEquiv ((ZMod N)ˣ × ZMod N × Bool) e.symm

namespace Data

/-- The clean temporary-flag convention for modular inversion. -/
def FlagClean {N : ℕ} (x : Data N) : Prop :=
  x.flag = false

/-- Add `u⁻¹` into the target register, preserving the input and flag. -/
def addInverseIntoTarget {N : ℕ} (x : Data N) : Data N where
  input := x.input
  target := x.target + inverseResidue x.input
  flag := x.flag

/-- Subtract `u⁻¹` from the target register, preserving the input and flag. -/
def subInverseFromTarget {N : ℕ} (x : Data N) : Data N where
  input := x.input
  target := x.target - inverseResidue x.input
  flag := x.flag

@[simp] theorem addInverseIntoTarget_input {N : ℕ} (x : Data N) :
    x.addInverseIntoTarget.input = x.input :=
  rfl

@[simp] theorem addInverseIntoTarget_target {N : ℕ} (x : Data N) :
    x.addInverseIntoTarget.target = x.target + inverseResidue x.input :=
  rfl

@[simp] theorem addInverseIntoTarget_flag {N : ℕ} (x : Data N) :
    x.addInverseIntoTarget.flag = x.flag :=
  rfl

@[simp] theorem subInverseFromTarget_input {N : ℕ} (x : Data N) :
    x.subInverseFromTarget.input = x.input :=
  rfl

@[simp] theorem subInverseFromTarget_target {N : ℕ} (x : Data N) :
    x.subInverseFromTarget.target = x.target - inverseResidue x.input :=
  rfl

@[simp] theorem subInverseFromTarget_flag {N : ℕ} (x : Data N) :
    x.subInverseFromTarget.flag = x.flag :=
  rfl

/-- Clean temporary flags remain clean after modular inversion. -/
theorem addInverseIntoTarget_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.addInverseIntoTarget.FlagClean :=
  h

/-- Clean temporary flags remain clean after inverse modular inversion. -/
theorem subInverseFromTarget_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.subInverseFromTarget.FlagClean :=
  h

/-- Unit-domain modular inversion as a reversible permutation. -/
def invEquiv (N : ℕ) : Equiv.Perm (Data N) where
  toFun := addInverseIntoTarget
  invFun := subInverseFromTarget
  left_inv := by
    intro x
    cases x
    simp [addInverseIntoTarget, subInverseFromTarget]
  right_inv := by
    intro x
    cases x
    simp [addInverseIntoTarget, subInverseFromTarget]

@[simp] theorem invEquiv_apply {N : ℕ} (x : Data N) :
    invEquiv N x = x.addInverseIntoTarget :=
  rfl

/-- Modular inversion with an external work register, leaving the work untouched. -/
def withWorkEquiv (N : ℕ) (Work : Type) : Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr (invEquiv N) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {N : ℕ} {Work : Type} (x : Data N) (w : Work) :
    withWorkEquiv N Work (x, w) = (x.addInverseIntoTarget, w) :=
  rfl

/-- The inversion map leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {N : ℕ} {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (withWorkEquiv N Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for unit-domain modular inversion. -/
def withWorkCleanMap (N : ℕ) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := withWorkEquiv N Work
  preservesWork := withWorkEquiv_preserves_work

end Data


end ModularInversion
end QuantumAlg
