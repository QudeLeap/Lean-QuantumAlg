/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse

/-!
# Actual saved-product readouts of the complete reused workspace

The original A payload and the complete Y word exchange their physical
roles. Every original padding, small history and pool wire retains its
identity. These symbolic readouts determine the saved-word orientation
without enumerating a fixed-width basis or running any extra SWAP.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse

noncomputable section

open BinaryLabelEncoding EncodedBit

private def originalBit (width : Nat) (bit : EncodedBit (SharedEEA.encoding width)) :
    EncodedBit (OutputCopy.encoding width) :=
  prodLeftBit (Scanned.encoding width) (finIdentity width) (Scanned.sourceBit width bit)

private def numeratorBit (width : Nat) (index : Fin width) :
    EncodedBit (OutputCopy.encoding width) :=
  prodRightBit (Scanned.encoding width) (finIdentity width) (finIdentityBit width index)

/-- Every original source read outside the A payload retains its actual physical value. -/
lemma grouping_original_read (width : Nat) (state : OutputCopy.Data width)
    (bit : EncodedBit (SharedEEA.encoding width)) (outside : width ≤ bit.wire.val) :
    bit.get ((placement width).grouping state).1.1 = bit.get state.1.1 := by
  let observed := originalBit width bit
  have location : ((placement width).placeBit observed).wire = observed.wire := by
    rw [placement, FullPlacement.ofWires_placeBit_wire]
    apply Fin.ext
    change address width bit.wire.val = bit.wire.val
    apply address_retained width bit.wire.val outside
    have sourceBound := bit.wire.isLt
    change bit.wire.val < (SharedEEA.encoding width).width + (poolEncoding width).width
    omega
  exact congrArg (fun lens : EncodedBit (OutputCopy.encoding width) => lens.get state)
    (EncodedBit.eq_of_wire_eq _ _ location)

/-- A's actual first width positions read the saved Y word in its physical order. -/
lemma grouping_large_bit (width : Nat) (state : OutputCopy.Data width) (index : Fin width) :
    ((placement width).grouping state).1.1.firstWord.getMsbD index.val =
      (finIdentityBit width index).get state.2 := by
  let source := originalBit width (firstWordBit width ⟨index.val, by omega⟩)
  let target := numeratorBit width index
  have location : ((placement width).placeBit source).wire = target.wire := by
    rw [placement, FullPlacement.ofWires_placeBit_wire]
    apply Fin.ext
    change address width index.val = (Scanned.encoding width).width + index.val
    exact address_accumulator width index
  have actual := congrArg (fun lens : EncodedBit (OutputCopy.encoding width) => lens.get state)
    (EncodedBit.eq_of_wire_eq _ _ location)
  simpa only [FullPlacement.placeBit, source, target, originalBit, numeratorBit,
    prodLeftBit, prodRightBit, Scanned.sourceBit_get, firstWordBit_get] using actual

/-- The complementary saved word reads A's same first width physical positions. -/
lemma grouping_numerator_bit (width : Nat) (state : OutputCopy.Data width) (index : Fin width) :
    (finIdentityBit width index).get ((placement width).grouping state).2 =
      state.1.1.firstWord.getMsbD index.val := by
  let source := numeratorBit width index
  let target := originalBit width (firstWordBit width ⟨index.val, by omega⟩)
  have location : ((placement width).placeBit source).wire = target.wire := by
    rw [placement, FullPlacement.ofWires_placeBit_wire]
    apply Fin.ext
    change address width ((Scanned.encoding width).width + index.val) = index.val
    exact address_numerator width index
  have actual := congrArg (fun lens : EncodedBit (OutputCopy.encoding width) => lens.get state)
    (EncodedBit.eq_of_wire_eq _ _ location)
  simpa only [FullPlacement.placeBit, source, target, originalBit, numeratorBit,
    prodLeftBit, prodRightBit, Scanned.sourceBit_get, firstWordBit_get] using actual

/-- The complete original X word, including all three original padding positions, is retained. -/
lemma grouping_secondWord (width : Nat) (state : OutputCopy.Data width) :
    ((placement width).grouping state).1.1.secondWord = state.1.1.secondWord := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := grouping_original_read width state (secondWordBit width ⟨index, within⟩)
    (by rw [secondWordBit_wire]; omega)
  simpa only [secondWordBit_get] using actual

/-- The original internal selector is independent of the reused A and Y payloads. -/
lemma grouping_control (width : Nat) (state : OutputCopy.Data width) :
    ((placement width).grouping state).1.1.control = state.1.1.control := by
  have actual := grouping_original_read width state (controlBit width)
    (by rw [controlBit_wire]; omega)
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse
