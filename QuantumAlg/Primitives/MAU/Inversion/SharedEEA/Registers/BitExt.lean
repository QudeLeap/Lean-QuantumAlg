/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.RegisterFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout

/-! # Equality of the complete shared EEA frame from physical bit readouts -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Registers

noncomputable section

/-- Retaining every actual bit retains all payload, metadata and control fields. -/
lemma eq_of_bit_get_eq {width : Nat} (left right : Registers width)
    (reads : ∀ bit : EncodedBit (encoding width), bit.get left = bit.get right) :
    left = right := by
  apply ext_fields
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    simpa only [firstWordBit_get] using reads (firstWordBit width ⟨index, within⟩)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    simpa only [secondWordBit_get] using reads (secondWordBit width ⟨index, within⟩)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    simpa only [coefficientLengthBit_get] using reads (coefficientLengthBit width ⟨index, within⟩)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    simpa only [quotientLengthBit_get] using reads (quotientLengthBit width ⟨index, within⟩)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    simpa only [divisorLengthBit_get] using reads (divisorLengthBit width ⟨index, within⟩)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    simpa only [shiftBit_get] using reads (shiftBit width ⟨index, within⟩)
  · exact reads (phase1Bit width)
  · exact reads (phase2Bit width)
  · exact reads (signBit width)
  · exact reads (iterationBit width)
  · exact reads (controlBit width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Registers
