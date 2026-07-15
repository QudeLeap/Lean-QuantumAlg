/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core
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

@[expose] public section

namespace QuantumAlg
namespace PlainAdder

/-- An `n`-bit word interpreted modulo `2^n`. -/
abbrev Word (n : ℕ) : Type :=
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

@[simp] theorem addIntoRight_left {n : ℕ} (x : Data n) :
    x.addIntoRight.left = x.left :=
  rfl

@[simp] theorem addIntoRight_right {n : ℕ} (x : Data n) :
    x.addIntoRight.right = x.right + x.left :=
  rfl

@[simp] theorem addIntoRight_carry {n : ℕ} (x : Data n) :
    x.addIntoRight.carry = x.carry :=
  rfl

@[simp] theorem subFromRight_left {n : ℕ} (x : Data n) :
    x.subFromRight.left = x.left :=
  rfl

@[simp] theorem subFromRight_right {n : ℕ} (x : Data n) :
    x.subFromRight.right = x.right - x.left :=
  rfl

@[simp] theorem subFromRight_carry {n : ℕ} (x : Data n) :
    x.subFromRight.carry = x.carry :=
  rfl

/-- Clean carry flags remain clean after addition. -/
theorem addIntoRight_preserves_clean {n : ℕ} (x : Data n)
    (h : x.CarryClean) : x.addIntoRight.CarryClean :=
  h

/-- Clean carry flags remain clean after subtraction. -/
theorem subFromRight_preserves_clean {n : ℕ} (x : Data n)
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

@[simp] theorem addEquiv_apply {n : ℕ} (x : Data n) :
    addEquiv n x = x.addIntoRight :=
  rfl

/-- The plain adder acting on an external work register, with work untouched. -/
def withWorkEquiv (n : ℕ) (Work : Type) : Equiv.Perm (Data n × Work) :=
  Equiv.prodCongr (addEquiv n) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {n : ℕ} {Work : Type} (x : Data n) (w : Work) :
    withWorkEquiv n Work (x, w) = (x.addIntoRight, w) :=
  rfl

/-- The plain adder leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {n : ℕ} {Work : Type} :
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

/-! ### Plain-adder gate wrapper -/

/-- Register whose basis labels are clean plain-adder data states. -/
def register (n : ℕ) : Register where
  Index := Data n
  fintype := inferInstance
  decEq := inferInstance

/-- The plain in-place adder, represented as a permutation gate on the
clean data-state basis. -/
noncomputable def addGate (n : ℕ) : Gate (register n) :=
  Gate.ofPerm (Data.addEquiv n).symm

/-- The plain-adder gate is unitary by construction as a permutation gate. -/
theorem addGate_mem_unitaryGroup (n : ℕ) :
    ((addGate n : Gate (register n)) : HilbertOperator (register n))
      ∈ Matrix.unitaryGroup (register n).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Clean basis action of the plain adder: `|a,b,0> ↦ |a,a+b,0>` over
`n`-bit words. -/
theorem addGate_apply_ket (n : ℕ) (x : Data n) :
    (addGate n).apply (PureState.ket (R := register n) x) =
      PureState.ket (R := register n) x.addIntoRight := by
  rw [addGate, Gate.ofPerm_apply_ket]
  rfl

/-! ### Resource skeleton -/

/-- Resource skeleton for a plain adder on two `n`-bit words and one clean carry
bit. Gate counts are parameters supplied by a source-specific counting pass. -/
def resourceProfile (n workQubits toffoliGates tGates cnotGates singleQubitGates
    circuitDepth toffoliDepth : ℕ) : ModularArithmeticResourceProfile where
  logicalQubits := 2 * n + 1 + workQubits
  dataQubits := 2 * n + 1
  workQubits := workQubits
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := toffoliGates
  tGates := tGates
  cnotGates := cnotGates
  singleQubitGates := singleQubitGates
  circuitDepth := circuitDepth
  toffoliDepth := toffoliDepth
  classicalArithmetic := ClassicalArithmeticProfile.zero

@[simp] theorem resourceProfile_logicalQubits
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).logicalQubits = 2 * n + 1 + workQubits :=
  rfl

@[simp] theorem resourceProfile_dataQubits
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).dataQubits = 2 * n + 1 :=
  rfl

@[simp] theorem resourceProfile_workQubits
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).workQubits = workQubits :=
  rfl

@[simp] theorem resourceProfile_oracleQueries
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).oracleQueries = 0 :=
  rfl

/-! ### Circuit witness -/

/-- Typed circuit witness for the plain in-place adder. The interpreted gate and
the projected resource profile are carried by the same `Circuit` object. -/
noncomputable def addCircuit
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) : Circuit (register n) :=
  Circuit.ofGate "plain-adder" (addGate n)
    (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).toResourceProfile
    circuitDepth 0

@[simp] theorem addCircuit_resources
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    (addCircuit n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).resources =
      (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
        circuitDepth toffoliDepth).toResourceProfile :=
  rfl

@[simp] theorem addCircuit_depth
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    (addCircuit n workQubits toffoliGates tGates cnotGates singleQubitGates
      circuitDepth toffoliDepth).depth = circuitDepth :=
  rfl

/-- Basis-state correctness for the typed plain-adder circuit witness. -/
theorem addCircuit_apply_ket
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) (x : Data n) :
    Circuit.apply
      (addCircuit n workQubits toffoliGates tGates cnotGates singleQubitGates
        circuitDepth toffoliDepth)
      (PureState.ket (R := register n) x : StateVector (register n)) =
      (PureState.ket (R := register n) x.addIntoRight : StateVector (register n)) := by
  simpa [addCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register n) => (psi : StateVector (register n)))
      (addGate_apply_ket n x)

/-- Correctness/resource proof package for a plain-adder circuit witness. -/
noncomputable def addCircuitResourceCorrectWitness
    (n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth : ℕ) :
    ResourceCorrectWitness (R := register n)
      (∀ x : Data n,
        Circuit.apply
          (addCircuit n workQubits toffoliGates tGates cnotGates singleQubitGates
            circuitDepth toffoliDepth)
          (PureState.ket (R := register n) x : StateVector (register n)) =
          (PureState.ket (R := register n) x.addIntoRight : StateVector (register n)))
      ((addCircuit n workQubits toffoliGates tGates cnotGates singleQubitGates
        circuitDepth toffoliDepth).resources =
        (resourceProfile n workQubits toffoliGates tGates cnotGates singleQubitGates
          circuitDepth toffoliDepth).toResourceProfile) where
  circuit :=
    addCircuit n workQubits toffoliGates tGates cnotGates singleQubitGates circuitDepth
      toffoliDepth
  correctness := by
    intro x
    exact addCircuit_apply_ket n workQubits toffoliGates tGates cnotGates
      singleQubitGates circuitDepth toffoliDepth x
  resources := by
    rfl

end PlainAdder
end QuantumAlg
