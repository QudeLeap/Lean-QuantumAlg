/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Addition.Coordinates

/-!
# Full-carry value of the actual metadata-address addition

Both operands retain their most-significant position. The high source bit
is the actual prefix padding bit even on dirty labels; its zero premise is
discharged only at the initialized scan boundary.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition

noncomputable section

open EncodedBit BinaryLabelEncoding NumberTheory.SharedEEA

/-- The full physical quotient addend includes the existing high padding bit. -/
def value (width : Nat) (state : Data width) : BitVec (ScanMetadata.addressWidth width) :=
  BitVec.cons ((AddressCopy.padding width).get state) state.1.quotientLength

private lemma source_get (width : Nat) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    ((source width).bit index).get state = (value width state).getMsbD index.val := by
  change ((source width).bit index).get state =
    (BitVec.cons ((AddressCopy.padding width).get state) state.1.quotientLength :
      BitVec (width.size + 1)).getMsbD index.val
  unfold source
  dsimp only
  split
  · rename_i zero
    simp only [zero, BitVec.getMsbD_cons_zero]
  · rename_i nonzero
    have successor : index.val = (index.val - 1) + 1 := by omega
    rw [sourceBit_get, quotientLengthBit_get]
    change state.1.quotientLength.getMsbD (index.val - 1) = _
    conv_rhs => rw [successor, BitVec.getMsbD_cons_succ]

private lemma firstLens_get (width : Nat) (index : Fin (ScanMetadata.addressWidth width))
    (pair : Addition.TTK.Registers (ScanMetadata.addressWidth width)) :
    (firstLens width index).get pair = (BitVec.ofFin pair.1).getMsbD index.val :=
  wordBit_get index (BitVec.ofFin pair.1)

private lemma secondLens_get (width : Nat) (index : Fin (ScanMetadata.addressWidth width))
    (pair : Addition.TTK.Registers (ScanMetadata.addressWidth width)) :
    (secondLens width index).get pair = (BitVec.ofFin pair.2).getMsbD index.val :=
  wordBit_get index (BitVec.ofFin pair.2)

/-- Grouping reads exactly the padded quotient, without changing its bit order. -/
lemma grouped_source_value (width : Nat) (state : Data width) :
    BitVec.ofFin (((placement width).full (source_total width)
      (encoding_surjective width)).grouping state).1.1 =
      value width state := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  exact (firstLens_get width ⟨index, within⟩ _).symm.trans
    ((grouped_source_get width state ⟨index, within⟩).trans (source_get width state _))

/-- Grouping reads the entire original address, including the carry position. -/
lemma grouped_target_value (width : Nat) (state : Data width) :
    BitVec.ofFin (((placement width).full (source_total width)
      (encoding_surjective width)).grouping state).1.2 =
      state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  exact (secondLens_get width ⟨index, within⟩ _).symm.trans
    ((grouped_target_get width state ⟨index, within⟩).trans (addressBit_get width _ state))

/-- The actual native body adds the complete quotient word to the complete address. -/
lemma step_address (width : Nat) (state : Data width) :
    (step width state).2.1 = value width state + state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have read := (placement width).full_step_source_read (source_total width)
    (encoding_surjective width) (secondLens width ⟨index, within⟩)
    (addressBit width ⟨index, within⟩) (second_location width ⟨index, within⟩)
    Addition.TTK.lowOutput state
  rw [secondLens_get] at read
  have sum : BitVec.ofFin
      (Addition.TTK.lowOutput
        (((placement width).full (source_total width)
          (encoding_surjective width)).grouping state).1).2 =
      value width state + state.2.1 := by
    change BitVec.ofFin
      (((placement width).full (source_total width)
        (encoding_surjective width)).grouping state).1.1 +
      BitVec.ofFin
      (((placement width).full (source_total width)
        (encoding_surjective width)).grouping state).1.2 = _
    rw [grouped_source_value, grouped_target_value]
  rw [sum] at read
  exact (addressBit_get width ⟨index, within⟩ (step width state)).symm.trans read

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition
