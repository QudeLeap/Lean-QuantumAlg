/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BasisMap.Contract
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Register
import all QuantumAlg.Core.Base.State.Normalized
public import Mathlib.Data.ZMod.Basic

/-!
# Plain reversible adders

This module records the clean mathematical interface for an in-place reversible
plain adder.  The word semantics are `ZMod (2^n)`: the adder preserves the left
input and a clean carry flag while adding the left word into the right word.
Concrete gate decompositions and source-specific counts are attached by later
modular-arithmetic modules.

The reversible-adder interface follows the elementary arithmetic-network route
where addition is the first reusable reversible block [VBE95,
9511018.tex:218-258, 591-604].
-/

section

namespace QuantumAlg
namespace PlainAdder

/-- An `n`-bit word interpreted modulo `2^n`. -/
public abbrev Word (n : ℕ) : Type :=
  ZMod (2 ^ n)

/-- Data registers for a plain in-place adder: left input, right target, and a
carry flag whose clean value is preserved. -/
structure Data (n : ℕ) where
  /-- Left data register component. -/
  left : Word n
  /-- Right data register component. -/
  right : Word n
  /-- Clean carry flag component. -/
  carry : Bool
deriving DecidableEq

instance instFintypeData (n : ℕ) : Fintype (Data n) := by
  classical
  let e : Data n ≃ (Word n × Word n × Bool) := {
    toFun := fun x => (x.left, (x.right, x.carry))
    invFun := fun x => { left := x.1, right := x.2.1, carry := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨left, rest⟩
      rcases rest with ⟨right, carry⟩
      rfl
  }
  exact Fintype.ofEquiv (Word n × Word n × Bool) e.symm

namespace Data

/-- The clean carry convention used by the plain-adder interface. -/
def CarryClean {n : ℕ} (x : Data n) : Prop :=
  x.carry = false

/-- Add the left word into the right word, preserving the left word and carry flag. -/
def addIntoRight {n : ℕ} (x : Data n) : Data n where
  left := x.left
  right := x.right + x.left
  carry := x.carry

/-- Inverse operation: subtract the left word from the right word. -/
def subFromRight {n : ℕ} (x : Data n) : Data n where
  left := x.left
  right := x.right - x.left
  carry := x.carry

@[simp] lemma addIntoRight_left {n : ℕ} (x : Data n) :
    x.addIntoRight.left = x.left :=
  rfl

@[simp] lemma addIntoRight_right {n : ℕ} (x : Data n) :
    x.addIntoRight.right = x.right + x.left :=
  rfl

@[simp] lemma addIntoRight_carry {n : ℕ} (x : Data n) :
    x.addIntoRight.carry = x.carry :=
  rfl

@[simp] lemma subFromRight_left {n : ℕ} (x : Data n) :
    x.subFromRight.left = x.left :=
  rfl

@[simp] lemma subFromRight_right {n : ℕ} (x : Data n) :
    x.subFromRight.right = x.right - x.left :=
  rfl

@[simp] lemma subFromRight_carry {n : ℕ} (x : Data n) :
    x.subFromRight.carry = x.carry :=
  rfl

/-- Clean carry flags remain clean after addition. -/
lemma addIntoRight_preserves_clean {n : ℕ} (x : Data n)
    (h : x.CarryClean) : x.addIntoRight.CarryClean :=
  h

/-- Clean carry flags remain clean after subtraction. -/
lemma subFromRight_preserves_clean {n : ℕ} (x : Data n)
    (h : x.CarryClean) : x.subFromRight.CarryClean :=
  h

/-- The plain adder as a reversible permutation of the data registers. -/
def addEquiv (n : ℕ) : Equiv.Perm (Data n) where
  toFun := addIntoRight
  invFun := subFromRight
  left_inv := by
    intro x
    cases x
    simp [addIntoRight, subFromRight]
  right_inv := by
    intro x
    cases x
    simp [addIntoRight, subFromRight]

@[simp] lemma addEquiv_apply {n : ℕ} (x : Data n) :
    addEquiv n x = x.addIntoRight :=
  rfl

/-- The plain adder acting on an external work register, with work untouched. -/
def withWorkEquiv (n : ℕ) (Work : Type) : Equiv.Perm (Data n × Work) :=
  Equiv.prodCongr (addEquiv n) (Equiv.refl Work)

@[simp] lemma withWorkEquiv_apply {n : ℕ} {Work : Type} (x : Data n) (w : Work) :
    withWorkEquiv n Work (x, w) = (x.addIntoRight, w) :=
  rfl

/-- The plain adder leaves the external work register clean. -/
lemma withWorkEquiv_preserves_work {n : ℕ} {Work : Type} :
    WorkRegister.Preserves (Data := Data n) (Work := Work) (withWorkEquiv n Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for a plain adder with an external work
register. -/
def withWorkCleanMap (n : ℕ) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data n) Work where
  perm := withWorkEquiv n Work
  preservesWork := withWorkEquiv_preserves_work

end Data

/-! ### Plain-adder unitary carrier -/

/-- Register whose basis labels are clean plain-adder data states. -/
@[implicit_reducible]
def register (n : ℕ) : Register where
  Index := Data n
  fintype := inferInstance
  decEq := inferInstance

/-- The plain in-place adder, represented as a permutation operator on the
clean data-state basis. -/
noncomputable def addOp (n : ℕ) : UnitaryOperator (register n) :=
  UnitaryOperator.ofPerm (Data.addEquiv n).symm

/-- Clean basis action of the plain adder: `|a,b,0> ↦ |a,a+b,0>` over
`n`-bit words. -/
lemma addOp_apply_ket (n : ℕ) (x : Data n) :
    (addOp n).apply (NormalizedVector.ket (R := register n) x) =
      NormalizedVector.ket (R := register n) x.addIntoRight := by
  rw [addOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-!
The executable plain-adder realization is intentionally not defined by this
semantic module.  `PlainAdder.Schedule.PowerOfTwo.carryWorkCircuit` is the
canonical sealed X/CNOT/Toffoli circuit.  Its cost and depth are recursive
projections of that circuit, and its clean-work endpoint is proved against the
same construction.  Keeping the realization in the schedule module prevents
callers from pairing `addOp` with an unrelated resource expression.
-/

end PlainAdder
end QuantumAlg

end
