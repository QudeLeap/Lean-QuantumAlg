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
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate

/-!
# Reversible modular multiplication by a unit

Multiplication by a unit of `ZMod N` is a permutation of all residues.  This is
the semantic permutation used by the modular-multiplication circuit target; the
binary-register action is exposed on valid canonical labels through the existing
residue encoding interface.

The clean multiplication-by-unit endpoint is represented as a MAC/swap/
inverse-MAC wrapper over the VBE-style elementary arithmetic route [VBE95,
9511018.tex:333-350]. Beauregard's compact Fourier-space construction and the
Gidney--Ekerå RSA envelope are cited as comparison/resource-envelope context,
not as exact structural support promoted here [Bea02, arxivfact.tex:129-146]
[GE19, main.tex:507-522].
-/

section

namespace QuantumAlg
namespace MAU.Multiplication

open QuantumAlg.ModularMultiplication

/-! ### Multiplication unitary carrier -/

/-- Register whose basis labels are residues modulo `N`. -/
@[implicit_reducible]
def residueRegister (N : ℕ) [NeZero N] : Register where
  Index := ZMod N
  fintype := inferInstance
  decEq := inferInstance

/-- The semantic modular-multiplication operator `U_{u,N}` on residue labels. -/
noncomputable def unitOp {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    UnitaryOperator (residueRegister N) :=
  UnitaryOperator.ofPerm (multiplyByUnitEquiv u).symm

/-- Basis action of multiplication by a unit: `U_u |x> = |u*x>`. -/
theorem unitOp_apply_ket {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (x : ZMod N) :
    (unitOp u).apply (NormalizedVector.ket (R := residueRegister N) x) =
      NormalizedVector.ket (R := residueRegister N) (multiplyByUnit u x) := by
  rw [unitOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-! ### Bridge to the modular-multiplication domain convention -/

/-- The residue action agrees with the existing unit-carrier multiplication
domain on the underlying residue. -/
private theorem domain_multiplyUnit_residue {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a x : ModularMultiplicationDomain.UnitCarrier D) :
    multiplyByUnit a (D.unitResidue x) = D.unitResidue (D.multiplyUnit a x) :=
  rfl

/-- On canonical encoded labels for units, the valid-label action agrees with
the existing modular-multiplication-domain canonical-label convention. -/
private theorem encoded_validAction_domain_canonicalLabel {N n : ℕ}
    (D : ModularMultiplicationDomain N n)
    (a x : ModularMultiplicationDomain.UnitCarrier D) :
    Encoded.validAction D.toBinaryResidueEncoding a (D.canonicalLabel x) =
      D.canonicalLabel (D.multiplyUnit a x) := by
  apply Fin.ext
  simp [Encoded.validAction, ModularMultiplicationDomain.canonicalLabel,
    ModularMultiplicationDomain.multiplyUnit, multiplyByUnit]

namespace Encoded

open QuantumAlg.ModularMultiplication.Encoded

/-- Total binary-label action for multiplication by a unit: canonical residue
labels follow multiplication by `u`, while padding labels are fixed. -/
def totalAction {N n : ℕ} (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if _hx : E.IsValid x then validAction E u x else x

@[simp] theorem totalAction_of_valid {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    totalAction E u x = validAction E u x := by
  simp [totalAction, hx]

@[simp] theorem totalAction_of_padding {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : ¬ E.IsValid x) :
    totalAction E u x = x := by
  simp [totalAction, hx]

private theorem validAction_isValid {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) (x : Fin (2 ^ n)) :
    E.IsValid (validAction E u x) :=
  E.encode_isValid _

private theorem decode_validAction {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) (x : Fin (2 ^ n)) :
    E.decode (validAction E u x) = multiplyByUnit u (E.decode x) :=
  E.decode_encode _

/-- The total multiplication action preserves canonical validity. -/
theorem totalAction_preservesValid {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    E.IsValid (totalAction E u x) := by
  simp [totalAction_of_valid E u x hx, validAction_isValid]

/-- The total multiplication action fixes padding labels. -/
theorem totalAction_preservesPadding {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : ¬ E.IsValid x) :
    ¬ E.IsValid (totalAction E u x) := by
  simpa [totalAction_of_padding E u x hx] using hx

/-- On canonical labels, the total action decodes to multiplication by `u`. -/
theorem decode_totalAction_of_valid {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    E.decode (totalAction E u x) = multiplyByUnit u (E.decode x) := by
  simpa [totalAction_of_valid E u x hx] using decode_validAction E u x

/-- Applying the valid-label multiplication action and then its inverse returns
the original canonical label. -/
theorem validAction_inv_left {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    validAction E u⁻¹ (validAction E u x) = x := by
  calc
    validAction E u⁻¹ (validAction E u x)
        = E.encode (multiplyByUnit u⁻¹ (E.decode (validAction E u x))) := rfl
    _ = E.encode (multiplyByUnit u⁻¹ (multiplyByUnit u (E.decode x))) := by
        rw [decode_validAction]
    _ = E.encode (E.decode x) := by
        simp [multiplyByUnit]
    _ = x := E.encode_decode_of_valid x hx

/-- Applying inverse valid-label multiplication and then the forward action
returns the original canonical label. -/
theorem validAction_inv_right {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    validAction E u (validAction E u⁻¹ x) = x := by
  calc
    validAction E u (validAction E u⁻¹ x)
        = E.encode (multiplyByUnit u (E.decode (validAction E u⁻¹ x))) := rfl
    _ = E.encode (multiplyByUnit u (multiplyByUnit u⁻¹ (E.decode x))) := by
        rw [decode_validAction]
    _ = E.encode (E.decode x) := by
        simp [multiplyByUnit]
    _ = x := E.encode_decode_of_valid x hx

/-- Total permutation of the binary residue-label space induced by
multiplication by a unit, fixing padding labels. -/
def totalPerm {N n : ℕ} (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := totalAction E u
  invFun := totalAction E u⁻¹
  left_inv := by
    intro x
    by_cases hx : E.IsValid x
    · have hvalid : E.IsValid (validAction E u x) :=
        validAction_isValid E u x
      rw [totalAction_of_valid E u x hx]
      rw [totalAction_of_valid E u⁻¹ (validAction E u x) hvalid]
      exact validAction_inv_left E u x hx
    · simp [totalAction_of_padding E u x hx, totalAction_of_padding E u⁻¹ x hx]
  right_inv := by
    intro x
    by_cases hx : E.IsValid x
    · have hvalid : E.IsValid (validAction E u⁻¹ x) :=
        validAction_isValid E u⁻¹ x
      rw [totalAction_of_valid E u⁻¹ x hx]
      rw [totalAction_of_valid E u (validAction E u⁻¹ x) hvalid]
      exact validAction_inv_right E u x hx
    · simp [totalAction_of_padding E u⁻¹ x hx, totalAction_of_padding E u x hx]

@[simp] theorem totalPerm_apply {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) :
    totalPerm E u x = totalAction E u x :=
  rfl

/-- Encoded residue basis-map contract for multiplication by a unit. -/
def totalContract {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) : EncodedResidueBasisMap E where
  perm := totalPerm E u
  residueMap := multiplyByUnit u
  preservesValid := totalAction_preservesValid E u
  preservesPadding := totalAction_preservesPadding E u
  action_on_valid := decode_totalAction_of_valid E u

end Encoded

/-! ### MAC / swap / uncompute construction -/

/-- Swap the multiplicand and accumulator registers in the MAC layout. -/
def swapMacRegisters {N : ℕ}
    (x : MAU.Multiplication.Accumulate.Data N) : MAU.Multiplication.Accumulate.Data N where
  multiplicand := x.accumulator
  accumulator := x.multiplicand
  flag := x.flag

@[simp] theorem swapMacRegisters_multiplicand {N : ℕ}
    (x : MAU.Multiplication.Accumulate.Data N) :
    (swapMacRegisters x).multiplicand = x.accumulator :=
  rfl

@[simp] theorem swapMacRegisters_accumulator {N : ℕ}
    (x : MAU.Multiplication.Accumulate.Data N) :
    (swapMacRegisters x).accumulator = x.multiplicand :=
  rfl

@[simp] theorem swapMacRegisters_flag {N : ℕ}
    (x : MAU.Multiplication.Accumulate.Data N) :
    (swapMacRegisters x).flag = x.flag :=
  rfl

/-- Swap as a reversible MAC-layout basis map. -/
def swapMacEquiv {N : ℕ} : Equiv.Perm (MAU.Multiplication.Accumulate.Data N) where
  toFun := swapMacRegisters
  invFun := swapMacRegisters
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

@[simp] theorem swapMacEquiv_apply {N : ℕ}
    (x : MAU.Multiplication.Accumulate.Data N) :
    swapMacEquiv x = swapMacRegisters x :=
  rfl

/-- MAC-register swap with an external work register, leaving work untouched. -/
def swapMacWithWorkEquiv {N : ℕ} (Work : Type) :
    Equiv.Perm (MAU.Multiplication.Accumulate.Data N × Work) :=
  Equiv.prodCongr swapMacEquiv (Equiv.refl Work)

@[simp] theorem swapMacWithWorkEquiv_apply {N : ℕ} {Work : Type}
    (x : MAU.Multiplication.Accumulate.Data N) (w : Work) :
    swapMacWithWorkEquiv Work (x, w) = (swapMacRegisters x, w) :=
  rfl

/-- The MAC-register swap leaves the external work register clean. -/
theorem swapMacWithWorkEquiv_preserves_work {N : ℕ} {Work : Type} :
    WorkRegister.Preserves
      (Data := MAU.Multiplication.Accumulate.Data N) (Work := Work)
      (swapMacWithWorkEquiv Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for the MAC-register swap. -/
def swapMacCleanMap {N : ℕ} (Work : Type) :
    WorkRegister.CleanReversibleMap (MAU.Multiplication.Accumulate.Data N) Work where
  perm := swapMacWithWorkEquiv Work
  preservesWork := swapMacWithWorkEquiv_preserves_work

@[simp] theorem swapMacCleanMap_perm_apply {N : ℕ} {Work : Type}
    (x : MAU.Multiplication.Accumulate.Data N) (w : Work) :
    (swapMacCleanMap (N := N) Work).perm (x, w) =
      (swapMacRegisters x, w) :=
  rfl

/-- Multiply by a unit through MAC, swap, and inverse uncomputation. -/
def macSwapUncompute {N : ℕ} (u : (ZMod N)ˣ)
    (x : MAU.Multiplication.Accumulate.Data N) : MAU.Multiplication.Accumulate.Data N :=
  (swapMacRegisters (x.addScaled (u : ZMod N))).subScaled ((u⁻¹ : (ZMod N)ˣ) : ZMod N)

/-- Certified clean reversible map for multiplication by a unit through MAC,
swap, and inverse uncomputation. -/
def macSwapUncomputeCleanMap {N : ℕ} (u : (ZMod N)ˣ) (Work : Type) :
    WorkRegister.CleanReversibleMap (MAU.Multiplication.Accumulate.Data N) Work :=
  WorkRegister.CleanReversibleMap.sequential
    (MAU.Multiplication.Accumulate.Data.withWorkCleanMap (u : ZMod N) Work)
    (WorkRegister.CleanReversibleMap.sequential
      (swapMacCleanMap (N := N) Work)
      (MAU.Multiplication.Accumulate.Data.withWorkCleanMap
        (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) Work).inverse)

@[simp] theorem macSwapUncomputeCleanMap_perm_apply {N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type}
    (x : MAU.Multiplication.Accumulate.Data N) (w : Work) :
    (macSwapUncomputeCleanMap u Work).perm (x, w) =
      (macSwapUncompute u x, w) := by
  simp [macSwapUncomputeCleanMap, macSwapUncompute,
    WorkRegister.CleanReversibleMap.sequential_perm,
    WorkRegister.CleanReversibleMap.inverse_perm,
    MAU.Multiplication.Accumulate.Data.withWorkCleanMap,
    MAU.Multiplication.Accumulate.Data.withWorkEquiv,
    MAU.Multiplication.Accumulate.Data.macEquiv]

/-- Clean input state for the MAC/swap/uncompute construction. -/
def cleanInput {N : ℕ} (x : ZMod N) : MAU.Multiplication.Accumulate.Data N where
  multiplicand := x
  accumulator := 0
  flag := false

/-- Clean output state for multiplication by a unit. -/
def cleanOutput {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    MAU.Multiplication.Accumulate.Data N where
  multiplicand := (u : ZMod N) * x
  accumulator := 0
  flag := false

/-- After the forward MAC and the physical register swap, the state is exactly
the clean output plus the inverse-unit multiple that the reverse MAC removes. -/
theorem swapMacRegisters_addScaled_cleanInput {N : ℕ}
    (u : (ZMod N)ˣ) (x : ZMod N) :
    swapMacRegisters ((cleanInput x).addScaled (u : ZMod N)) =
      (cleanOutput u x).addScaled
        (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
  ext <;> simp [cleanInput, cleanOutput, swapMacRegisters,
    MAU.Multiplication.Accumulate.Data.addScaled]

/-- Correctness of the MAC/swap/inverse-uncompute construction on clean input. -/
theorem macSwapUncompute_cleanInput {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    macSwapUncompute u (cleanInput x) = cleanOutput u x := by
  ext <;> simp [macSwapUncompute, cleanInput, cleanOutput, swapMacRegisters,
    MAU.Multiplication.Accumulate.Data.addScaled, MAU.Multiplication.Accumulate.Data.subScaled]

/-- The MAC/swap/inverse-uncompute wrapper realizes the residue multiplication
action while restoring the accumulator and clean flag. The exact structural
route is the VBE-style MAC support [VBE95, 9511018.tex:333-350]; Beauregard and
Gidney--Ekerå provide comparison/resource-envelope context, not theorem-node
promotion for this wrapper [Bea02, arxivfact.tex:129-146] [GE19,
main.tex:507-522]. -/
theorem macSwapUncompute_cleanInput_multiplyByUnit {N : ℕ}
    (u : (ZMod N)ˣ) (x : ZMod N) :
    macSwapUncompute u (cleanInput x) =
      ({ multiplicand := multiplyByUnit u x
         accumulator := 0
         flag := false } : MAU.Multiplication.Accumulate.Data N) := by
  simpa [cleanOutput, multiplyByUnit] using
    macSwapUncompute_cleanInput u x

/-- The certified clean map realizes multiplication by a unit on clean input
while preserving the external work register. -/
theorem macSwapUncomputeCleanMap_perm_cleanInput {N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type} (x : ZMod N) (w : Work) :
    (macSwapUncomputeCleanMap u Work).perm (cleanInput x, w) =
      (cleanOutput u x, w) := by
  rw [macSwapUncomputeCleanMap_perm_apply, macSwapUncompute_cleanInput]

/-- The certified clean map realizes the public multiplication-by-unit residue
action and restores the external work register, accumulator, and clean flag. -/
private theorem macSwapUncomputeCleanMap_perm_cleanInput_multiplyByUnit {N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type} (x : ZMod N) (w : Work) :
    (macSwapUncomputeCleanMap u Work).perm (cleanInput x, w) =
      (({ multiplicand := multiplyByUnit u x
          accumulator := 0
          flag := false } : MAU.Multiplication.Accumulate.Data N), w) := by
  rw [macSwapUncomputeCleanMap_perm_apply, macSwapUncompute_cleanInput_multiplyByUnit]

end MAU.Multiplication
end QuantumAlg

end
