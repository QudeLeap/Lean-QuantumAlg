/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BasisMap
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.CleanInterface

/-!
# Reversible modular addition

This module records the clean reversible map for modular addition over `ZMod N`
and the arithmetic lemma behind the compare/subtract/add-back route: for
canonical representatives, subtracting `N` exactly when the plain sum overflows
computes reduction modulo `N`.

The clean modular-addition route follows the reversible compare/subtract/add-back
network used in elementary arithmetic constructions [VBE95,
9511018.tex:274-316, 634-643]. Beauregard's Fourier-space variant is tracked as
a source route but remains separate from the exact-count endpoint until its
approximation policy is discharged [Bea02, arxivfact.tex:97-118].
-/

section

namespace QuantumAlg
namespace MAU.Addition

/-- Data registers for an in-place modular adder. The clean flag represents the
temporary comparison/borrow information after uncomputation. -/
structure Data (N : ℕ) where
  /-- Left data register component. -/
  left : ZMod N
  /-- Right data register component. -/
  right : ZMod N
  /-- Clean control or comparison flag component. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (N : ℕ) [NeZero N] : Fintype (Data N) := by
  classical
  let e : Data N ≃ (ZMod N × ZMod N × Bool) := {
    toFun := fun x => (x.left, (x.right, x.flag))
    invFun := fun x => { left := x.1, right := x.2.1, flag := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨left, rest⟩
      rcases rest with ⟨right, flag⟩
      rfl
  }
  exact Fintype.ofEquiv (ZMod N × ZMod N × Bool) e.symm

namespace Data

/-- The clean flag convention for modular addition. -/
def FlagClean {N : ℕ} (x : Data N) : Prop :=
  x.flag = false

/-- Add the left residue into the right residue modulo `N`, preserving the flag. -/
def addIntoRight {N : ℕ} (x : Data N) : Data N where
  left := x.left
  right := x.right + x.left
  flag := x.flag

/-- Inverse operation for the modular adder. -/
def subFromRight {N : ℕ} (x : Data N) : Data N where
  left := x.left
  right := x.right - x.left
  flag := x.flag

@[simp] theorem addIntoRight_left {N : ℕ} (x : Data N) :
    x.addIntoRight.left = x.left :=
  rfl

@[simp] theorem addIntoRight_right {N : ℕ} (x : Data N) :
    x.addIntoRight.right = x.right + x.left :=
  rfl

@[simp] theorem addIntoRight_flag {N : ℕ} (x : Data N) :
    x.addIntoRight.flag = x.flag :=
  rfl

@[simp] theorem subFromRight_left {N : ℕ} (x : Data N) :
    x.subFromRight.left = x.left :=
  rfl

@[simp] theorem subFromRight_right {N : ℕ} (x : Data N) :
    x.subFromRight.right = x.right - x.left :=
  rfl

@[simp] theorem subFromRight_flag {N : ℕ} (x : Data N) :
    x.subFromRight.flag = x.flag :=
  rfl

/-- Clean temporary flags remain clean after modular addition. -/
theorem addIntoRight_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.addIntoRight.FlagClean :=
  h

/-- Clean temporary flags remain clean after modular subtraction. -/
theorem subFromRight_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.subFromRight.FlagClean :=
  h

/-- Modular addition as a reversible permutation on residue data registers. -/
def addEquiv (N : ℕ) : Equiv.Perm (Data N) where
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

@[simp] theorem addEquiv_apply {N : ℕ} (x : Data N) :
    addEquiv N x = x.addIntoRight :=
  rfl

/-- Modular addition with an external work register, leaving the work untouched. -/
def withWorkEquiv (N : ℕ) (Work : Type) : Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr (addEquiv N) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {N : ℕ} {Work : Type} (x : Data N) (w : Work) :
    withWorkEquiv N Work (x, w) = (x.addIntoRight, w) :=
  rfl

/-- The modular adder leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {N : ℕ} {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (withWorkEquiv N Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for modular addition with an external work
register. -/
def withWorkCleanMap (N : ℕ) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := withWorkEquiv N Work
  preservesWork := withWorkEquiv_preserves_work

end Data

/-! ### ADD_N unitary carrier -/

/-- Register whose basis labels are clean modular-addition data states. -/
@[implicit_reducible]
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The modular-addition operator `ADD_N`, represented as a permutation on the
clean data-state basis. -/
noncomputable def addOp (N : ℕ) [NeZero N] : UnitaryOperator (register N) :=
  UnitaryOperator.ofPerm (Data.addEquiv N).symm

/-- Clean basis action of `ADD_N`: `|a,b,0> ↦ |a,a+b mod N,0>`. -/
theorem addOp_apply_ket (N : ℕ) [NeZero N] (x : Data N) :
    (addOp N).apply (NormalizedVector.ket (R := register N) x) =
      NormalizedVector.ket (R := register N) x.addIntoRight := by
  rw [addOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-! ### Same-circuit realization -/

/-- A concrete typed-circuit realization of modular addition. The semantic
operator, correctness theorem, cost, and depth all refer to the one stored
circuit. -/
structure CircuitRealization (N : ℕ) [NeZero N] where
  /-- The executable typed circuit. -/
  circuit : UnitaryCircuit (register N)
  /-- The circuit implements the modular-addition operator. -/
  matrix_eq : circuit.matrix = addOp N

namespace CircuitRealization

variable {N : ℕ} [NeZero N]

/-- Ordered strict events derived from the realization circuit. -/
def eventTrace (realization : CircuitRealization N) :
    List (Resource.Event .quantum) :=
  realization.circuit.eventTrace

/-- Strict event pool derived from the realization circuit. -/
def eventCost (realization : CircuitRealization N) : ResourcePool .quantum :=
  realization.circuit.eventCost

/-- Strict symbolic event critical path of the realization circuit. -/
def eventDepth (realization : CircuitRealization N) :
    DepthExpr (Resource.Event .quantum) :=
  realization.circuit.eventDepth

/-- Literal depth of one strict event coordinate in the realization circuit. -/
def eventQueryDepth (realization : CircuitRealization N)
    (focus : Resource.Event .quantum) : Nat :=
  realization.circuit.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the realization circuit. -/
def eventGateCount (realization : CircuitRealization N)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) realization.circuit.eventCost

/-- Linearizing the realization's event depth recovers its exact event pool. -/
theorem resourcesFromEventDepth_eq_eventCost
    (realization : CircuitRealization N) :
    realization.circuit.resourcesFromEventDepth = realization.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost realization.circuit





/-- Intrinsically normalized basis action of the realized modular adder. -/
theorem applyNormalized_ket (realization : CircuitRealization N) (x : Data N) :
    realization.circuit.applyNormalized
        (NormalizedVector.ket (R := register N) x) =
      NormalizedVector.ket (R := register N) x.addIntoRight := by
  change realization.circuit.matrix.apply
      (NormalizedVector.ket (R := register N) x) = _
  rw [realization.matrix_eq]
  exact addOp_apply_ket N x

/-- Clean public-form basis action `|a,b,0⟩ ↦ |a,a+b,0⟩`. -/
theorem applyNormalized_clean_ket (realization : CircuitRealization N)
    (a b : ZMod N) :
    realization.circuit.applyNormalized
        (NormalizedVector.ket (R := register N)
          ({ left := a, right := b, flag := false } : Data N)) =
      NormalizedVector.ket (R := register N)
        ({ left := a, right := a + b, flag := false } : Data N) := by
  simpa [Data.addIntoRight, add_comm] using
    realization.applyNormalized_ket
      ({ left := a, right := b, flag := false } : Data N)

end CircuitRealization

/-- Same-circuit realization type for modular addition with an external clean
work register. Concrete base-gate schedules construct this interface. -/
abbrev WithWorkCircuitRealization (N : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work] :=
  WorkRegister.CleanReversibleMap.CircuitRealization
    (Data.withWorkCleanMap N Work)

/-! ### Compare/subtract/add-back route -/

/-- Natural-number representative produced by comparing `a+b` against `N` and
subtracting `N` exactly on overflow. -/
def compareSubtractAddBack (N a b : ℕ) : ℕ :=
  if N ≤ a + b then a + b - N else a + b

/-- For canonical representatives, compare/subtract/add-back is reduction modulo `N`. -/
theorem compareSubtractAddBack_eq_mod {N a b : ℕ}
    (_hN : 0 < N) (ha : a < N) (hb : b < N) :
    compareSubtractAddBack N a b = (a + b) % N := by
  unfold compareSubtractAddBack
  by_cases hoverflow : N ≤ a + b
  · have hlt : a + b - N < N := by omega
    rw [if_pos hoverflow, Nat.mod_eq_sub_mod hoverflow, Nat.mod_eq_of_lt hlt]
  · have hlt : a + b < N := by omega
    rw [if_neg hoverflow, Nat.mod_eq_of_lt hlt]

/-- The compare/subtract/add-back representative denotes modular addition in `ZMod N`. -/
private theorem natCast_compareSubtractAddBack {N a b : ℕ}
    (hN : 0 < N) (ha : a < N) (hb : b < N) :
    (compareSubtractAddBack N a b : ZMod N) = (a : ZMod N) + (b : ZMod N) := by
  rw [compareSubtractAddBack_eq_mod hN ha hb]
  simp [Nat.cast_add]

end MAU.Addition
end QuantumAlg

end
