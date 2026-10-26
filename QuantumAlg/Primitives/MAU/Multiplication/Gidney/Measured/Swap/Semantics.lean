/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout.Readout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Prefix
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Complete original-word and clean-frame semantics of the actual controlled exchange

The full native word exchanges the two original word readouts exactly on
the selected original control branch. Helpers, flag, control and every
outside encoded wire retain their original values
[VBE95, 9511018.tex:333-367; G25, main.tex:354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual source word is the original target on the selected branch. -/
lemma swapWordGates_sourceWord (layout : Layout encoding width) (state : Data) :
    layout.sourceWord (stepList layout.swapWordGates state) =
      if layout.control.get state then layout.targetWord state else layout.sourceWord state := by
  cases chosen : layout.control.get state
  · change BitVec.ofFnLE (fun index =>
      (layout.source index).get (stepList layout.swapWordGates state)) =
        BitVec.ofFnLE (fun index => (layout.source index).get state)
    congr 1
    funext observed
    have actual := (swapPrefixGates_readouts layout width le_rfl state observed).1
    simpa only [swapWordGates, if_pos observed.isLt, chosen, Bool.false_eq_true, if_false]
      using actual
  · change BitVec.ofFnLE (fun index =>
      (layout.source index).get (stepList layout.swapWordGates state)) =
        BitVec.ofFnLE (fun index => (layout.target index).get state)
    congr 1
    funext observed
    have actual := (swapPrefixGates_readouts layout width le_rfl state observed).1
    simpa only [swapWordGates, if_pos observed.isLt, chosen, if_true] using actual

/-- The actual target word is the original source on the selected branch. -/
lemma swapWordGates_targetWord (layout : Layout encoding width) (state : Data) :
    layout.targetWord (stepList layout.swapWordGates state) =
      if layout.control.get state then layout.sourceWord state else layout.targetWord state := by
  cases chosen : layout.control.get state
  · change BitVec.ofFnLE (fun index =>
      (layout.target index).get (stepList layout.swapWordGates state)) =
        BitVec.ofFnLE (fun index => (layout.target index).get state)
    congr 1
    funext observed
    have actual := (swapPrefixGates_readouts layout width le_rfl state observed).2
    simpa only [swapWordGates, if_pos observed.isLt, chosen, Bool.false_eq_true, if_false]
      using actual
  · change BitVec.ofFnLE (fun index =>
      (layout.target index).get (stepList layout.swapWordGates state)) =
        BitVec.ofFnLE (fun index => (layout.source index).get state)
    congr 1
    funext observed
    have actual := (swapPrefixGates_readouts layout width le_rfl state observed).2
    simpa only [swapWordGates, if_pos observed.isLt, chosen, if_true] using actual

/-- The actual full controlled word exchange retains the same original global control. -/
lemma swapWordGates_control (layout : Layout encoding width) (state : Data) :
    layout.control.get (stepList layout.swapWordGates state) = layout.control.get state :=
  swapPrefixGates_control layout width le_rfl state

/-- Every actual native exchange retains both original clean helpers without preparation. -/
lemma swapWordGates_clean (layout : Layout encoding width) (state : Data) (helper : Fin 2) :
    (layout.clean helper).get (stepList layout.swapWordGates state) =
      (layout.clean helper).get state :=
  swapPrefixGates_preserves_projection layout width le_rfl (layout.clean helper).get
    (fun _ => get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    (fun _ => get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    state

/-- The original reduction flag is retained by the entire actual controlled exchange. -/
lemma swapWordGates_flag (layout : Layout encoding width) (state : Data) :
    layout.flag.get (stepList layout.swapWordGates state) = layout.flag.get state :=
  swapPrefixGates_preserves_projection layout width le_rfl layout.flag.get
    (fun _ => get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    (fun _ => get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    state

/-- Every encoded outside-wire readout is retained by the same actual native exchange. -/
lemma swapWordGates_outside (layout : Layout encoding width) (state : Data)
    (observed : Fin encoding.width) (outside : ∀ port, (layout.bit port).wire ≠ observed) :
    (encoding.encode (stepList layout.swapWordGates state)).val.testBit
      (WireAddress.bitIndex observed).val =
        (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  apply swapPrefixGates_preserves_projection layout width le_rfl
    (fun current => (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val)
  · intro index current
    have separated : (layout.source index).wire ≠ observed := outside (.inr (.inl index))
    rw [(layout.source index).encode_flip, WireAddress.bit_flipBit_of_ne separated]
  · intro index current
    have separated : (layout.target index).wire ≠ observed := outside (.inr (.inr (.inl index)))
    rw [(layout.target index).encode_flip, WireAddress.bit_flipBit_of_ne separated]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
