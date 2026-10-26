/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Copy
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Orientation
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Interleave
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Compose

/-!
# Complete original three-word coordinates for externally controlled inversion

The original scanned source and its pool precede the retained numerator
and C/N/W. The same full placement selects C and W and reverses all
Work2 addresses at both endpoints of the actual inversion program.
The numerator, N, every history field and pool position remain present.
All constructions are symbolic in the original width.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame

noncomputable section

open QuantumAlg.EncodedBit

abbrev Flags := Bool × (Bool × Bool)

def flagsEncoding : BinaryLabelEncoding Flags := .prod .bool (.prod .bool .bool)

abbrev Data (width : Nat) := OutputCopy.Data width × Flags

def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  .prod (OutputCopy.encoding width) flagsEncoding

def savedEncoding (width : Nat) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width) BinaryLabelEncoding.bool

abbrev Grouped (width : Nat) := ControlledFrame.Data width × (Fin (2 ^ width) × Bool)

def groupedEncoding (width : Nat) : BinaryLabelEncoding (Grouped width) :=
  .prod (ControlledFrame.encoding width) (savedEncoding width)

private def selectedLayout (width : Nat) :
    FullPlacement (groupedEncoding width) (encoding width) :=
  FullPlacement.Interleave.placement (Scanned.encoding width)
    (BinaryLabelEncoding.finIdentity width)

private def orientation (width : Nat) : FullPlacement (encoding width) (encoding width) :=
  (((OutputOrientation.placement width).appendRight (poolEncoding width)).appendRight
    (BinaryLabelEncoding.finIdentity width)).appendRight flagsEncoding

/-- The selected systems and complete Work2 reversal follow the same native address map. -/
def layout (width : Nat) : FullPlacement (groupedEncoding width) (encoding width) :=
  (selectedLayout width).compose (orientation width)

/-- Reassemble all original physical components, including arbitrary retained Y, N and W. -/
def reassemble (width : Nat) (state : Grouped width) : Data width :=
  (((((OutputOrientation.grouping width).symm state.1.1.1), state.1.1.2), state.2.1),
    (state.1.2.1, (state.2.2, state.1.2.2)))

lemma layout_grouping (width : Nat) (state : Data width) :
    (layout width).grouping state =
      ((((OutputOrientation.grouping width state.1.1.1), state.1.1.2),
        (state.2.1, state.2.2.2)), (state.1.2, state.2.2.1)) := by
  change (((((OutputOrientation.placement width).grouping state.1.1.1), state.1.1.2),
    (state.2.1, state.2.2.2)), (state.1.2, state.2.2.1)) = _
  rw [OutputOrientation.placement_grouping]

/-- Both endpoint labels use the exact inverse of the same complete physical grouping. -/
lemma layout_reassemble (width : Nat) (state : Grouped width) :
    (layout width).grouping.symm state = reassemble width state := by
  apply (layout width).grouping.injective
  rw [Equiv.apply_symm_apply, layout_grouping]
  simp only [reassemble, Equiv.apply_symm_apply]

/-- Numerical coefficient on the original resident Work2 payload. -/
def value {width : Nat} (state : Data width) : Fin (2 ^ width) :=
  SharedEEA.OutputCopy.value state.1.1.1

/-- Original Work2 is reversed as a full word, including all three original padding positions. -/
lemma reassemble_value (width : Nat) (state : Grouped width) :
    (value (reassemble width state)).val = state.1.1.1.secondWord.toNat % 2 ^ width := by
  change (state.1.1.1.secondWord.reverse.reverse.setWidth width).toNat = _
  rw [BitVec.reverse_reverse_eq, BitVec.toNat_setWidth]

lemma reassemble_numerator (width : Nat) (state : Grouped width) :
    (reassemble width state).1.2 = state.2.1 := rfl

lemma reassemble_pool (width : Nat) (state : Grouped width) :
    (reassemble width state).1.1.2 = state.1.1.2 := rfl

lemma reassemble_flags (width : Nat) (state : Grouped width) :
    (reassemble width state).2 = (state.1.2.1, (state.2.2, state.1.2.2)) := rfl

/-- Actual three-word frame plus the three original supplied suffix systems. -/
lemma p256_encoding_width : (encoding 256).width = 839 := by
  change (Scanned.encoding 256).width + 256 + (1 + (1 + 1)) = 839
  rw [Scanned.p256_encoding_width]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame
