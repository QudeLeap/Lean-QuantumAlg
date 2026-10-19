/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BasisMap
import all QuantumAlg.Util.ModularMultiplicationDomain
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# Reversible modular multiply-accumulate

This module fixes the reusable multiply-accumulate convention used by modular
multiplication and exponentiation support.  For a constant `a : ZMod N`, the
map preserves the multiplicand and clean flag while updating the accumulator by
`y ↦ y + a*x`.

The uniform fixed-layout realization from repeated controlled modular additions
is provided by `MAU.Multiplication.Accumulate.VBECircuit` [VBE95,
9511018.tex:333-367]. Gidney--Ekerå use the same modular-arithmetic vocabulary
inside their RSA resource envelope [GE19, main.tex:511-519]; that citation is
resource-route context rather than an independent exact construction promoted
here.
-/

section

namespace QuantumAlg
namespace MAU.Multiplication.Accumulate

/-- Data registers for a modular multiply-accumulate map. -/
structure Data (N : ℕ) where
  /-- Multiplicand register value for multiply-accumulate data. -/
  multiplicand : ZMod N
  /-- Accumulator register value for multiply-accumulate data. -/
  accumulator : ZMod N
  /-- Clean control or comparison flag component. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (N : ℕ) [NeZero N] : Fintype (Data N) := by
  classical
  let e : Data N ≃ (ZMod N × ZMod N × Bool) := {
    toFun := fun x => (x.multiplicand, (x.accumulator, x.flag))
    invFun := fun x => { multiplicand := x.1, accumulator := x.2.1, flag := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨multiplicand, rest⟩
      rcases rest with ⟨accumulator, flag⟩
      rfl
  }
  exact Fintype.ofEquiv (ZMod N × ZMod N × Bool) e.symm

namespace Data

/-- Extensionality for MAC data registers. -/
@[ext] lemma ext {N : ℕ} {x y : Data N}
    (hmultiplicand : x.multiplicand = y.multiplicand)
    (haccumulator : x.accumulator = y.accumulator)
    (hflag : x.flag = y.flag) : x = y := by
  cases x
  cases y
  simp_all

/-- The clean flag convention for multiply-accumulate. -/
def FlagClean {N : ℕ} (x : Data N) : Prop :=
  x.flag = false

/-- Add `a * multiplicand` into the accumulator. -/
def addScaled {N : ℕ} (a : ZMod N) (x : Data N) : Data N where
  multiplicand := x.multiplicand
  accumulator := x.accumulator + a * x.multiplicand
  flag := x.flag

/-- Inverse operation for `addScaled`. -/
def subScaled {N : ℕ} (a : ZMod N) (x : Data N) : Data N where
  multiplicand := x.multiplicand
  accumulator := x.accumulator - a * x.multiplicand
  flag := x.flag

@[simp] lemma addScaled_multiplicand {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.addScaled a).multiplicand = x.multiplicand :=
  rfl

@[simp] lemma addScaled_accumulator {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.addScaled a).accumulator = x.accumulator + a * x.multiplicand :=
  rfl

@[simp] lemma addScaled_flag {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.addScaled a).flag = x.flag :=
  rfl

@[simp] lemma subScaled_multiplicand {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.subScaled a).multiplicand = x.multiplicand :=
  rfl

@[simp] lemma subScaled_accumulator {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.subScaled a).accumulator = x.accumulator - a * x.multiplicand :=
  rfl

@[simp] lemma subScaled_flag {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.subScaled a).flag = x.flag :=
  rfl

/-- Clean flags remain clean after multiply-accumulate. -/
private lemma addScaled_preserves_clean {N : ℕ} (a : ZMod N) (x : Data N)
    (h : x.FlagClean) : (x.addScaled a).FlagClean :=
  h

/-- Clean flags remain clean after inverse multiply-accumulate. -/
private lemma subScaled_preserves_clean {N : ℕ} (a : ZMod N) (x : Data N)
    (h : x.FlagClean) : (x.subScaled a).FlagClean :=
  h

/-- Reversible multiply-accumulate permutation for a fixed constant `a`. -/
def macEquiv {N : ℕ} (a : ZMod N) : Equiv.Perm (Data N) where
  toFun := addScaled a
  invFun := subScaled a
  left_inv := by
    intro x
    cases x
    simp [addScaled, subScaled]
  right_inv := by
    intro x
    cases x
    simp [addScaled, subScaled]

@[simp] lemma macEquiv_apply {N : ℕ} (a : ZMod N) (x : Data N) :
    macEquiv a x = x.addScaled a :=
  rfl

/-- Boolean-control convention: `false` is identity and `true` applies MAC. -/
def controlledApply {N : ℕ} (a : ZMod N) (control : Bool) (x : Data N) : Data N :=
  if control then x.addScaled a else x

@[simp] lemma controlledApply_false {N : ℕ} (a : ZMod N) (x : Data N) :
    controlledApply a false x = x := by
  simp [controlledApply]

@[simp] lemma controlledApply_true {N : ℕ} (a : ZMod N) (x : Data N) :
    controlledApply a true x = x.addScaled a := by
  simp [controlledApply]

/-- Multiply-accumulate with an external work register, leaving work untouched. -/
def withWorkEquiv {N : ℕ} (a : ZMod N) (Work : Type) :
    Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr (macEquiv a) (Equiv.refl Work)

@[simp] lemma withWorkEquiv_apply {N : ℕ} (a : ZMod N) {Work : Type}
    (x : Data N) (w : Work) :
    withWorkEquiv a Work (x, w) = (x.addScaled a, w) :=
  rfl

/-- The MAC convention leaves the external work register clean. -/
lemma withWorkEquiv_preserves_work {N : ℕ} (a : ZMod N) {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (withWorkEquiv a Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for multiply-accumulate with an external
work register. -/
def withWorkCleanMap {N : ℕ} (a : ZMod N) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := withWorkEquiv a Work
  preservesWork := withWorkEquiv_preserves_work a

end Data

/-! ### MAC unitary carrier -/

/-- Register whose basis labels are clean multiply-accumulate data states. -/
@[implicit_reducible]
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The fixed-constant multiply-accumulate operator, represented as a permutation
on the clean data-state basis. -/
noncomputable def macOp {N : ℕ} [NeZero N] (a : ZMod N) :
    UnitaryOperator (register N) :=
  UnitaryOperator.ofPerm (Data.macEquiv a).symm

/-- Clean basis action of the MAC gate:
`|x,y,0> ↦ |x,y+a*x,0>`. -/
lemma macOp_apply_ket {N : ℕ} [NeZero N] (a : ZMod N) (x : Data N) :
    (macOp a).apply (NormalizedVector.ket (R := register N) x) =
      NormalizedVector.ket (R := register N) (x.addScaled a) := by
  rw [macOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

end MAU.Multiplication.Accumulate
end QuantumAlg

end
