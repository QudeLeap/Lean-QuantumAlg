/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic

/-! # Complete physical bit readouts determine a fully encoded state -/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Every physical position of a complete encoding has its exact mathematical bit lens. -/
def fullBit (onto : Function.Surjective encoding.encode) (wire : Fin encoding.width) :
    EncodedBit encoding where
  wire := wire
  get state := (encoding.encode state).val.testBit (WireAddress.bitIndex wire).val
  flip state := (Equiv.ofBijective encoding.encode ⟨encoding.encode_injective, onto⟩).symm
    (WireAddress.flipBit wire (encoding.encode state))
  get_eq _ := rfl
  encode_flip _ :=
    (Equiv.ofBijective encoding.encode ⟨encoding.encode_injective, onto⟩).apply_symm_apply _

/-- Keeping every physical readout is a complete state equality, including arbitrary workspace. -/
lemma state_eq_of_get_eq (onto : Function.Surjective encoding.encode) (first second : Data)
    (reads : ∀ observed : EncodedBit encoding, observed.get first = observed.get second) :
    first = second := by
  apply encoding.encode_injective
  apply (BinaryBasis.bigEndianEquiv encoding.width).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  have actual := reads (fullBit onto index)
  have position : (WireAddress.bitIndex index).val = index.rev.val := by
    rw [WireAddress.bitIndex_val, Fin.val_rev]
    omega
  simpa only [fullBit, position] using actual

end

end QuantumAlg.EncodedBit
