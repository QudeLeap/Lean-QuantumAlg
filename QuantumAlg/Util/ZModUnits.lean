/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.ResidueEncoding

/-!
# Unit actions on `ZMod`

This module contains quantum-free helpers for multiplication by units modulo
`N` and their action on valid binary residue labels. Circuit wrappers live in
the primitive layer; the residue/unit arithmetic itself is reusable utility
material.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularMultiplication

/-- Multiplication by a unit on residues modulo `N`. -/
def multiplyByUnit {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) : ZMod N :=
  (u : ZMod N) * x

/-- Multiplication by a unit is a residue permutation. -/
def multiplyByUnitEquiv {N : ℕ} (u : (ZMod N)ˣ) : Equiv.Perm (ZMod N) where
  toFun := multiplyByUnit u
  invFun := fun x => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x
  left_inv := by
    intro x
    simp [multiplyByUnit]
  right_inv := by
    intro x
    simp [multiplyByUnit]

@[simp] theorem multiplyByUnitEquiv_apply {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    multiplyByUnitEquiv u x = (u : ZMod N) * x :=
  rfl

/-- A coprime natural representative determines a unit modulo `N`. -/
def unitOfCoprime {N a : ℕ} (h : Nat.Coprime a N) : (ZMod N)ˣ :=
  ZMod.unitOfCoprime a h

@[simp] theorem unitOfCoprime_coe {N a : ℕ} (h : Nat.Coprime a N) :
    (unitOfCoprime (N := N) (a := a) h : ZMod N) = a :=
  ZMod.coe_unitOfCoprime a h

/-- Multiplication by a coprime natural representative as a residue permutation. -/
def multiplyByCoprimeEquiv {N a : ℕ} (h : Nat.Coprime a N) : Equiv.Perm (ZMod N) :=
  multiplyByUnitEquiv (unitOfCoprime (N := N) (a := a) h)

@[simp] theorem multiplyByCoprimeEquiv_apply {N a : ℕ} (h : Nat.Coprime a N)
    (x : ZMod N) :
    multiplyByCoprimeEquiv h x = (a : ZMod N) * x := by
  simp [multiplyByCoprimeEquiv]

/-! ### Encoded valid-label action -/

namespace Encoded

/-- Valid-label action induced by multiplication by a unit. Padding policy is
handled by the later total register-level contract; this function is only the canonical
residue action on valid labels. -/
def validAction {N n : ℕ} (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  E.encode (multiplyByUnit u (E.decode x))

private theorem validAction_isValid {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) (x : Fin (2 ^ n)) :
    E.IsValid (validAction E u x) :=
  E.encode_isValid _

private theorem decode_validAction {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) (x : Fin (2 ^ n)) :
    E.decode (validAction E u x) = multiplyByUnit u (E.decode x) :=
  E.decode_encode _

end Encoded

end ModularMultiplication
end QuantumAlg
