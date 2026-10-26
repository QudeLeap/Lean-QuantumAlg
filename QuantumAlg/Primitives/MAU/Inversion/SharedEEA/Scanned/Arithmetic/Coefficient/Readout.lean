/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Frame

/-! # Original coefficient operand readouts and the complete unchanged metadata and pool -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientFrame

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The source template reads each actual coefficient operand at its original physical bit. -/
lemma grouped_template_bit (width : Nat) (first : Bool) (index : Fin (width + 3))
    (state : Data width) :
    (ArithmeticTemplate.wordBit width first index).get ((placement width).grouping state) =
      (ArithmeticRotation.bit width (!first) index).get state :=
  FullPlacement.ofWires_read (encoding width) (encoding width)
    (Scanned.encoding_surjective width) (Scanned.encoding_surjective width) (wires width)
    (ArithmeticTemplate.wordBit width first index) (ArithmeticRotation.bit width (!first) index)
    (wires_wordBit width first index) state

/-- Static operand placement leaves every original source read outside the two words unchanged. -/
lemma grouped_retained_bit (width : Nat) (bit : EncodedBit (encoding width))
    (outside : 2 * (width + 3) ≤ bit.wire.val) (state : Data width) :
    bit.get ((placement width).grouping state) = bit.get state :=
  FullPlacement.ofWires_read (encoding width) (encoding width)
    (Scanned.encoding_surjective width) (Scanned.encoding_surjective width) (wires width)
    bit bit (wires_retained width bit.wire outside) state

/-- The full original address, prefix and conjunction retain their exact encoded values. -/
lemma grouped_pool (width : Nat) (state : Data width) :
    ((placement width).grouping state).2 = state.2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (addressBit width ⟨index, within⟩).wire.val := by
      rw [addressBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [addressBit_get] using
      grouped_retained_bit width (addressBit width ⟨index, within⟩) outside state
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (prefixBit width ⟨index, within⟩).wire.val := by
      rw [prefixBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [prefixBit_get] using
      grouped_retained_bit width (prefixBit width ⟨index, within⟩) outside state
  · apply grouped_retained_bit width (conjunctionBit width)
    rw [conjunctionBit_wire, SharedEEA.encoding_width]
    omega

/-- The same original root control enables the statically placed coefficient arithmetic. -/
lemma grouped_control (width : Nat) (state : Data width) :
    ((placement width).grouping state).1.control = state.1.control := by
  apply grouped_retained_bit width (sourceBit width (SharedEEA.controlBit width))
  rw [sourceBit_wire, SharedEEA.controlBit_wire]
  omega

/-- Original Sign remains the same arbitrary overflow output under the physical placement. -/
lemma grouped_sign (width : Nat) (state : Data width) :
    ((placement width).grouping state).1.flags.sign = state.1.flags.sign := by
  apply grouped_retained_bit width (sourceBit width (SharedEEA.signBit width))
  rw [sourceBit_wire, SharedEEA.signBit_wire]
  omega

/-- The original arbitrary dirty Iter retains its complete coherent value. -/
lemma grouped_iteration (width : Nat) (state : Data width) :
    ((placement width).grouping state).1.flags.iteration = state.1.flags.iteration := by
  apply grouped_retained_bit width (sourceBit width (SharedEEA.iterationBit width))
  rw [sourceBit_wire, SharedEEA.iterationBit_wire]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientFrame
