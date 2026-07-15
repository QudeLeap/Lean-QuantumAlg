/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Util.ResidueEncoding

/-!
# Encoded residue basis-map contracts

This module gives reusable contracts for reversible maps on binary registers
that encode residues modulo `N`. A contract is a total permutation of the binary
labels together with the induced residue-level action on canonical labels and a
policy that padding labels remain padding.

The contract isolates the reversible-map obligations used by the source
arithmetic networks: valid residue labels evolve by the stated modular action,
while auxiliary and padding data are restored or kept outside the valid domain
so the resulting operation can be used coherently inside order finding [VBE95,
9511018.tex:83-106, 294-316] [Bea02, arxivfact.tex:108-118, 127-146] [GE19,
main.tex:511-519].
-/

@[expose] public section

namespace QuantumAlg

/-- Reversible basis-map contract for a binary register encoding residues modulo
`N`.

The permutation is total on all `Fin (2^n)` labels. Valid labels below `N` stay
valid and follow the stated `residueMap`; padding labels stay outside the valid
domain. -/
structure EncodedResidueBasisMap {N n : ℕ} (E : BinaryResidueEncoding N n) where
  /-- Permutation implementing the reversible basis map. -/
  perm : Equiv.Perm (Fin (2 ^ n))
  /-- Residue-level function tracked by the encoded basis permutation. -/
  residueMap : ZMod N → ZMod N
  preservesValid : ∀ x : Fin (2 ^ n), E.IsValid x → E.IsValid (perm x)
  preservesPadding : ∀ x : Fin (2 ^ n), ¬ E.IsValid x → ¬ E.IsValid (perm x)
  action_on_valid :
    ∀ x : Fin (2 ^ n), (hx : E.IsValid x) →
      E.decode (perm x) = residueMap (E.decode x)

namespace EncodedResidueBasisMap

variable {N n : ℕ} {E : BinaryResidueEncoding N n}

/-- Identity basis-map contract for an encoded residue register. -/
def identity (E : BinaryResidueEncoding N n) : EncodedResidueBasisMap E where
  perm := Equiv.refl (Fin (2 ^ n))
  residueMap := id
  preservesValid := by
    intro x hx
    exact hx
  preservesPadding := by
    intro x hx
    exact hx
  action_on_valid := by
    intro x _hx
    rfl

@[simp]
theorem identity_perm (E : BinaryResidueEncoding N n) (x : Fin (2 ^ n)) :
    (identity E).perm x = x := rfl

@[simp]
theorem identity_residueMap (E : BinaryResidueEncoding N n) (z : ZMod N) :
    (identity E).residueMap z = z := rfl

/-- Sequential composition: apply `first`, then `second`. -/
def sequential (first second : EncodedResidueBasisMap E) : EncodedResidueBasisMap E where
  perm := first.perm.trans second.perm
  residueMap := fun z => second.residueMap (first.residueMap z)
  preservesValid := by
    intro x hx
    exact second.preservesValid (first.perm x) (first.preservesValid x hx)
  preservesPadding := by
    intro x hx
    exact second.preservesPadding (first.perm x) (first.preservesPadding x hx)
  action_on_valid := by
    intro x hx
    have hfirst : E.IsValid (first.perm x) := first.preservesValid x hx
    calc
      E.decode ((first.perm.trans second.perm) x)
          = E.decode (second.perm (first.perm x)) := rfl
      _ = second.residueMap (E.decode (first.perm x)) :=
          second.action_on_valid (first.perm x) hfirst
      _ = second.residueMap (first.residueMap (E.decode x)) := by
          rw [first.action_on_valid x hx]

/-- Gate implementing the basis-map contract. The inverse is passed to
`Gate.ofPerm` so that the ket action is `x ↦ perm x`. -/
noncomputable def gate (contract : EncodedResidueBasisMap E) : Gate (Qubits n) :=
  Gate.ofPerm contract.perm.symm

@[simp]
theorem sequential_perm (first second : EncodedResidueBasisMap E) (x : Fin (2 ^ n)) :
    (sequential first second).perm x = second.perm (first.perm x) := rfl

@[simp]
theorem sequential_residueMap (first second : EncodedResidueBasisMap E) (z : ZMod N) :
    (sequential first second).residueMap z = second.residueMap (first.residueMap z) := rfl

/-- Inverse basis-map contract. Its residue action is defined by decoding the
inverse permutation applied to the canonical encoding of the input residue. -/
def inverse (contract : EncodedResidueBasisMap E) : EncodedResidueBasisMap E where
  perm := contract.perm.symm
  residueMap := fun z => E.decode (contract.perm.symm (E.encode z))
  preservesValid := by
    intro x hx
    by_contra hbad
    exact contract.preservesPadding (contract.perm.symm x) hbad (by simpa)
  preservesPadding := by
    intro x hx hvalid
    exact hx (by simpa using contract.preservesValid (contract.perm.symm x) hvalid)
  action_on_valid := by
    intro x hx
    have hxround : E.encode (E.decode x) = x := E.encode_decode_of_valid x hx
    simp [hxround]

@[simp]
theorem inverse_perm (contract : EncodedResidueBasisMap E) (x : Fin (2 ^ n)) :
    contract.inverse.perm x = contract.perm.symm x := rfl

@[simp]
theorem inverse_residueMap (contract : EncodedResidueBasisMap E) (z : ZMod N) :
    contract.inverse.residueMap z = E.decode (contract.perm.symm (E.encode z)) := rfl

private theorem sequential_inverse_left_perm
    (contract : EncodedResidueBasisMap E) (x : Fin (2 ^ n)) :
    (sequential contract.inverse contract).perm x = x := by
  simp [sequential_perm]

private theorem sequential_inverse_right_perm
    (contract : EncodedResidueBasisMap E) (x : Fin (2 ^ n)) :
    (sequential contract contract.inverse).perm x = x := by
  simp [sequential_perm]

/-- Basis-state action of the gate implementing an encoded residue basis map. -/
theorem gate_apply_ket (contract : EncodedResidueBasisMap E) (x : Fin (2 ^ n)) :
    contract.gate.apply (PureState.ket x) = PureState.ket (contract.perm x) := by
  simpa [gate] using Gate.ofPerm_apply_ket (R := Qubits n) contract.perm.symm x

/-- On canonical residue labels, the total basis permutation agrees with the
contract's residue-level map and returns a canonical label. -/
theorem perm_encode_eq (contract : EncodedResidueBasisMap E) (z : ZMod N) :
    contract.perm (E.encode z) = E.encode (contract.residueMap z) := by
  have hcanonical : E.IsValid (E.encode z) := E.encode_isValid z
  have hvalid : E.IsValid (contract.perm (E.encode z)) :=
    contract.preservesValid (E.encode z) hcanonical
  calc
    contract.perm (E.encode z)
        = E.encode (E.decode (contract.perm (E.encode z))) := by
          exact (E.encode_decode_of_valid (contract.perm (E.encode z)) hvalid).symm
    _ = E.encode (contract.residueMap z) := by
          rw [contract.action_on_valid (E.encode z) hcanonical]
          simp

end EncodedResidueBasisMap

/-! ### Work-register preservation -/

namespace WorkRegister

variable {Data Work Control : Type}

/-- A permutation on a data/work product preserves the work register when the
second component is unchanged for every input. -/
def Preserves (sigma : Equiv.Perm (Data × Work)) : Prop :=
  ∀ x : Data × Work, (sigma x).2 = x.2

theorem preserves_refl : Preserves (Equiv.refl (Data × Work)) := by
  intro x
  rfl

theorem preserves_sequential {first second : Equiv.Perm (Data × Work)}
    (hfirst : Preserves first) (hsecond : Preserves second) :
    Preserves (first.trans second) := by
  intro x
  calc
    ((first.trans second) x).2 = (second (first x)).2 := rfl
    _ = (first x).2 := hsecond (first x)
    _ = x.2 := hfirst x

theorem preserves_inverse {sigma : Equiv.Perm (Data × Work)} (h : Preserves sigma) :
    Preserves sigma.symm := by
  intro x
  have hx := h (sigma.symm x)
  simpa using hx.symm

/-- Iterated sequential product of the same work-preserving permutation. -/
def iterate : ℕ → Equiv.Perm (Data × Work) → Equiv.Perm (Data × Work)
  | 0, _sigma => Equiv.refl (Data × Work)
  | k + 1, sigma => (iterate k sigma).trans sigma

@[simp]
theorem iterate_zero (sigma : Equiv.Perm (Data × Work)) :
    iterate 0 sigma = Equiv.refl (Data × Work) := rfl

@[simp]
theorem iterate_succ (k : ℕ) (sigma : Equiv.Perm (Data × Work)) :
    iterate (k + 1) sigma = (iterate k sigma).trans sigma := rfl

theorem preserves_iterate (k : ℕ) {sigma : Equiv.Perm (Data × Work)}
    (h : Preserves sigma) : Preserves (iterate k sigma) := by
  induction k with
  | zero =>
      exact preserves_refl
  | succ k ih =>
      exact preserves_sequential ih h

/-- Controlled work-register permutation. The control is part of the data side;
the final work component has the same type and position as in the uncontrolled
body. -/
def controlled [DecidableEq Control] (controlValue : Control)
    (body : Equiv.Perm (Data × Work)) : Equiv.Perm ((Control × Data) × Work) where
  toFun x :=
    if h : x.1.1 = controlValue then
      let y := body (x.1.2, x.2)
      ((x.1.1, y.1), y.2)
    else
      x
  invFun x :=
    if h : x.1.1 = controlValue then
      let y := body.symm (x.1.2, x.2)
      ((x.1.1, y.1), y.2)
    else
      x
  left_inv := by
    intro x
    rcases x with ⟨⟨c, d⟩, w⟩
    by_cases h : c = controlValue
    · rw [h]
      simp
    · simp [h]
  right_inv := by
    intro x
    rcases x with ⟨⟨c, d⟩, w⟩
    by_cases h : c = controlValue
    · rw [h]
      simp
    · simp [h]

theorem preserves_controlled [DecidableEq Control] (controlValue : Control)
    {body : Equiv.Perm (Data × Work)} (hbody : Preserves body) :
    Preserves (controlled (Control := Control) (Data := Data) (Work := Work)
      controlValue body) := by
  intro x
  rcases x with ⟨⟨c, d⟩, w⟩
  by_cases h : c = controlValue
  · rw [h]
    simpa [controlled] using hbody (d, w)
  · simp [controlled, h]

/-! #### Certified clean reversible maps -/

/-- A reusable reversible map on data/work registers together with a certificate
that the work register is preserved. This is the shared clean-ancilla interface
consumed by modular-arithmetic primitives. -/
structure CleanReversibleMap (Data Work : Type) where
  /-- Permutation implementing the reversible basis map. -/
  perm : Equiv.Perm (Data × Work)
  preservesWork : Preserves perm

namespace CleanReversibleMap

variable {Data Work Control : Type}

/-- Identity clean reversible map. -/
def identity (Data Work : Type) : CleanReversibleMap Data Work where
  perm := Equiv.refl (Data × Work)
  preservesWork := preserves_refl

/-- Sequential composition of clean reversible maps. -/
def sequential (first second : CleanReversibleMap Data Work) :
    CleanReversibleMap Data Work where
  perm := first.perm.trans second.perm
  preservesWork := preserves_sequential first.preservesWork second.preservesWork

/-- Inverse of a clean reversible map. -/
def inverse (clean : CleanReversibleMap Data Work) :
    CleanReversibleMap Data Work where
  perm := clean.perm.symm
  preservesWork := preserves_inverse clean.preservesWork

/-- Iterated sequential composition of a clean reversible map. -/
def iterate (k : ℕ) (clean : CleanReversibleMap Data Work) :
    CleanReversibleMap Data Work where
  perm := WorkRegister.iterate k clean.perm
  preservesWork := preserves_iterate k clean.preservesWork

/-- Controlled clean reversible map. The control is treated as part of the data
side, while the same work register is preserved. -/
def controlled [DecidableEq Control] (controlValue : Control)
    (clean : CleanReversibleMap Data Work) :
    CleanReversibleMap (Control × Data) Work where
  perm := WorkRegister.controlled (Control := Control) (Data := Data) (Work := Work)
    controlValue clean.perm
  preservesWork := preserves_controlled controlValue clean.preservesWork

@[simp]
theorem identity_perm (x : Data × Work) :
    (identity Data Work).perm x = x :=
  rfl

@[simp]
theorem sequential_perm (first second : CleanReversibleMap Data Work)
    (x : Data × Work) :
    (sequential first second).perm x = second.perm (first.perm x) :=
  rfl

@[simp]
theorem inverse_perm (clean : CleanReversibleMap Data Work) (x : Data × Work) :
    clean.inverse.perm x = clean.perm.symm x :=
  rfl

end CleanReversibleMap

end WorkRegister

end QuantumAlg
