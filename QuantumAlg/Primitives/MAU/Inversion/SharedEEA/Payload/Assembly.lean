/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Preparation

/-!
# Exact basis assembly for input and retained arithmetic payload

The single-input source assembly keeps every auxiliary and Work2 address.
All supplied payload bits follow that complete frame unchanged. The basis
map is a representation correspondence proved at every physical coordinate;
it introduces no gate or uncharged wire permutation. Arbitrary fresh basis
values and both zero widths are supported [LYL+26, sec_EEA/sub_regshare.tex:16-26].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PayloadAssembly

noncomputable section

open Execution PayloadPreparation

private def oldEquiv (width payloadWidth : Nat) :
    (before width payloadWidth).register.Index ≃
      ((InputPreparation.before width).register.Index × Fin (2 ^ payloadWidth)) :=
  (inputBasisEquiv width payloadWidth).trans
    (Equiv.prodCongr (InputPreparation.inputBasisEquiv width).symm (Equiv.refl _))

/-- The single-input source assembly and the payload both retain their exact wire identities. -/
def basisEquiv (width payloadWidth : Nat) :
    (after width payloadWidth).register.Index ≃ (Qubits (frameEncoding width
      payloadWidth).width).Index :=
  (assembly width payloadWidth).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (oldEquiv width payloadWidth)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr
          ((InputAssembly.assembly width).trans (InputAssembly.basisEquiv width))
          (Equiv.refl _)).trans (prodEquiv (m := (encoding width).width) (n := payloadWidth)))))

/-- Read the first original word through the already proved original input basis. -/
def oldInput (width payloadWidth : Nat) (old : (before width payloadWidth).register.Index) :
    (InputPreparation.before width).register.Index :=
  (InputPreparation.inputBasisEquiv width).symm ((inputBasisEquiv width payloadWidth old).1)

/-- Exact assembly holds for all auxiliary values and arbitrary input and payload. -/
theorem payloadAssembly_basisEquiv_assembly (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) :
    basisEquiv width payloadWidth (assembly width payloadWidth (fresh, old)) =
      prodEquiv (m := (encoding width).width) (n := payloadWidth)
        (InputAssembly.basisEquiv width
          (InputAssembly.assembly width (fresh, oldInput width payloadWidth old)),
          (inputBasisEquiv width payloadWidth old).2) := by
  let encodePair :
      ((InputPreparation.auxiliaryLayout width).register.Index × (before width
        payloadWidth).register.Index) →
        (Qubits (frameEncoding width payloadWidth).width).Index := fun pair =>
    prodEquiv (m := (encoding width).width) (n := payloadWidth)
      (InputAssembly.basisEquiv width
        (InputAssembly.assembly width (pair.1, oldInput width payloadWidth pair.2)),
        (inputBasisEquiv width payloadWidth pair.2).2)
  change encodePair ((assembly width payloadWidth).symm (assembly width payloadWidth (fresh,
    old))) = encodePair (fresh, old)
  exact congrArg encodePair ((assembly width payloadWidth).symm_apply_apply (fresh, old))

/-- An auxiliary wire keeps its already declared source identity in the complete input/payload
  layout. -/
def auxiliaryPosition (width payloadWidth : Nat) (index : Fin (InputPreparation.auxiliaryWidth
  width)) :
    Fin (frameEncoding width payloadWidth).width :=
  ⟨(InputAssembly.auxiliaryPosition width index).val, by
    have bound := (InputAssembly.auxiliaryPosition width index).isLt
    change _ < (encoding width).width + payloadWidth
    omega⟩

/-- The original first input remains at its source Work2 physical address. -/
def inputPosition (width payloadWidth : Nat) (index : Fin width) : Fin (frameEncoding width
  payloadWidth).width :=
  ⟨(InputAssembly.inputPosition width index).val, by
    have bound := (InputAssembly.inputPosition width index).isLt
    change _ < (encoding width).width + payloadWidth
    omega⟩

/-- The supplied payload remains after the original complete source frame. -/
def payloadPosition (width payloadWidth : Nat) (index : Fin payloadWidth) : Fin (frameEncoding
  width payloadWidth).width :=
  ⟨(encoding width).width + index.val, by
    have bound := index.isLt
    change _ < (encoding width).width + payloadWidth
    omega⟩

private theorem auxiliary_rev (width payloadWidth : Nat)
    (index : Fin (InputPreparation.auxiliaryWidth width)) :
    (auxiliaryPosition width payloadWidth index).rev.val =
      payloadWidth + (InputAssembly.auxiliaryPosition width index).rev.val := by
  simp only [auxiliaryPosition, Fin.val_rev]
  change (encoding width).width + payloadWidth - (_ + 1) = _
  have bound := (InputAssembly.auxiliaryPosition width index).isLt
  omega

private theorem input_rev (width payloadWidth : Nat) (index : Fin width) :
    (inputPosition width payloadWidth index).rev.val =
      payloadWidth + (InputAssembly.inputPosition width index).rev.val := by
  simp only [inputPosition, Fin.val_rev]
  change (encoding width).width + payloadWidth - (_ + 1) = _
  have bound := (InputAssembly.inputPosition width index).isLt
  omega

private theorem payload_rev (width payloadWidth : Nat) (index : Fin payloadWidth) :
    (payloadPosition width payloadWidth index).rev.val = index.rev.val := by
  simp only [payloadPosition, Fin.val_rev]
  change (encoding width).width + payloadWidth - ((encoding width).width + index.val + 1) = _
  omega

/-- Every auxiliary position retains its actual original value, with input and payload arbitrary. -/
theorem payloadAssembly_basisEquiv_auxiliary (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) (index : Fin
      (InputPreparation.auxiliaryWidth width)) :
    (basisEquiv width payloadWidth (assembly width payloadWidth (fresh, old))).val.testBit
      (auxiliaryPosition width payloadWidth index).rev.val = finTwoEquiv (fresh index) := by
  rw [payloadAssembly_basisEquiv_assembly, auxiliary_rev, prodEquiv_testBit_left]
  exact InputAssembly.basisEquiv_auxiliary width fresh (oldInput width payloadWidth old) index

/-- Every original input bit retains its actual source identity in the joint assembly. -/
theorem payloadAssembly_basisEquiv_input (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) (index : Fin width) :
    (basisEquiv width payloadWidth (assembly width payloadWidth (fresh, old))).val.testBit
      (inputPosition width payloadWidth index).rev.val =
        (inputBasisEquiv width payloadWidth old).1.val.testBit index.rev.val := by
  rw [payloadAssembly_basisEquiv_assembly, input_rev, prodEquiv_testBit_left]
  have actual := InputAssembly.basisEquiv_input width fresh (oldInput width payloadWidth old) index
  simpa only [oldInput, Equiv.apply_symm_apply] using actual

/-- Every supplied payload bit retains its original rightmost physical identity and value. -/
theorem payloadAssembly_basisEquiv_payload (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) (index : Fin payloadWidth) :
    (basisEquiv width payloadWidth (assembly width payloadWidth (fresh, old))).val.testBit
      (payloadPosition width payloadWidth index).rev.val =
        (inputBasisEquiv width payloadWidth old).2.val.testBit index.rev.val := by
  rw [payloadAssembly_basisEquiv_assembly, payload_rev, prodEquiv_testBit_right]

/-- The fixed preparation produces exactly the literal source initial frame and arbitrary
  payload. -/
theorem payloadAssembly_prepared_initial (modulus payloadWidth : Nat) (old : (before
  modulus.size payloadWidth).register.Index) :
    basisEquiv modulus.size payloadWidth
        (assembly modulus.size payloadWidth ((InputPreparation.preparation modulus).value, old)) =
      (frameEncoding modulus.size payloadWidth).encode
        (InitialFrame.initial modulus (inputBasisEquiv modulus.size payloadWidth old).1,
          (inputBasisEquiv modulus.size payloadWidth old).2) := by
  rw [payloadAssembly_basisEquiv_assembly]
  have source := InputPreparedFrame.basisEquiv_prepared_initial modulus
    (oldInput modulus.size payloadWidth old)
  have exactInput : InputPreparation.inputBasisEquiv modulus.size (oldInput modulus.size
    payloadWidth old) =
      (inputBasisEquiv modulus.size payloadWidth old).1 :=
    (InputPreparation.inputBasisEquiv modulus.size).apply_symm_apply _
  rw [exactInput] at source
  exact congrArg
    (fun frame : Fin (2 ^ (encoding modulus.size).width) =>
      prodEquiv (m := (encoding modulus.size).width) (n := payloadWidth)
        (frame, (inputBasisEquiv modulus.size payloadWidth old).2)) source

end

end QuantumAlg.MAU.Inversion.SharedEEA.PayloadAssembly
