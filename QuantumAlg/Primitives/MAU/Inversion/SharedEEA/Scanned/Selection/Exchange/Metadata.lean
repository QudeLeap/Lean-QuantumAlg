/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange

/-!
# The selected payload retains every metadata input of address and enable preparation

The exact physical Sign/Work1 exchange cannot inspect or change any length
or phase coordinate. These full-label identities let the actual inverse
address preparation reuse the same source fields after the payload.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma metadata_get (width : Nat) (index : Fin (width + 3))
    (observed : EncodedBit (SharedEEA.encoding width))
    (beyondWord : width + 3 ≤ observed.wire.val)
    (notSign : (SharedEEA.signBit width).wire ≠ observed.wire) (state : Data width) :
    observed.get (action width index state).1 = observed.get state.1 := by
  have wordNe : (firstWordBit width index).wire ≠ observed.wire := by
    intro same
    have values := congrArg Fin.val same
    rw [firstWordBit_wire] at values
    have within := index.isLt
    omega
  exact swapStep_get_observed_of_swap_ne _ _ (sourceBit width observed)
    (targets_ne width index) (source_source_ne width _ _ notSign)
    (source_source_ne width _ _ wordNe) state

/-- Every complete coefficient-length word is unchanged by the selected exchange. -/
lemma action_coefficient (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    (action width index state).1.coefficientLength = state.1.coefficientLength := by
  apply BitVec.eq_of_getMsbD_eq
  intro bit within
  have actual := metadata_get width index (coefficientLengthBit width ⟨bit, within⟩)
    (by rw [coefficientLengthBit_wire]; omega)
    (by intro same; have values := congrArg Fin.val same
        rw [signBit_wire, coefficientLengthBit_wire] at values; omega) state
  simpa only [coefficientLengthBit_get] using actual

/-- Every complete quotient-length word is unchanged, including out-of-trajectory finite labels. -/
lemma action_quotient (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    (action width index state).1.quotientLength = state.1.quotientLength := by
  apply BitVec.eq_of_getMsbD_eq
  intro bit within
  have actual := metadata_get width index (quotientLengthBit width ⟨bit, within⟩)
    (by rw [quotientLengthBit_wire]; omega)
    (by intro same; have values := congrArg Fin.val same
        rw [signBit_wire, quotientLengthBit_wire] at values; omega) state
  simpa only [quotientLengthBit_get] using actual

/-- Phase1 is retained, so the physical address carry correction can be unprepared. -/
lemma action_phase1 (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    (action width index state).1.flags.first = state.1.flags.first :=
  metadata_get width index (phase1Bit width)
    (by rw [phase1Bit_wire]; omega)
    (by intro same; have values := congrArg Fin.val same
        rw [signBit_wire, phase1Bit_wire] at values; omega) state

/-- Phase2 is retained, so the paid phase-enable preparation can be uncomputed. -/
lemma action_phase2 (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    (action width index state).1.flags.second = state.1.flags.second :=
  metadata_get width index (phase2Bit width)
    (by rw [phase2Bit_wire]; omega)
    (by intro same; have values := congrArg Fin.val same
        rw [signBit_wire, phase2Bit_wire] at values; omega) state

/-- The full natural address is the same before and after the selected native payload. -/
lemma action_address (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    ScanMetadata.address (action width index state).1.coefficientLength
      (action width index state).1.quotientLength (action width index state).1.flags.first =
      ScanMetadata.address state.1.coefficientLength state.1.quotientLength
        state.1.flags.first := by
  rw [action_coefficient, action_quotient, action_phase1]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange
