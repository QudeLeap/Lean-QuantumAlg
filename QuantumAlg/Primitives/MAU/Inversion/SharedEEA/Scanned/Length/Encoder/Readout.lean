/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Readout
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Position

/-!
# Actual complete first-one readout on the original EEA frame

The existing address is an arbitrary XOR target. Only the existing prefix
starts zero; the original control, source, Iter and other word are arbitrary.
The nontruncated natural readout separately requires the sentinel to fit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Zero in the actual complete prefix supplies every strict future traversal bit. -/
lemma clean_of_prefix_zero (width : Nat) (field : Field) (first : Bool) (state : Data width)
    (zero : state.2.2.1 = 0) : (frame width field first).CleanFrom 0 state := by
  intro index later
  change (SelectionFrame.stack width index).get state = false
  unfold SelectionFrame.stack
  rw [dif_neg (show index.val ≠ 0 by omega), prefixBit_get, zero]
  exact BitVec.getMsbD_zero

/-- The retained encoder root is exactly the original EEA control. -/
lemma root_get (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    ((frame width field first).stack.bit ⟨0, by omega⟩).get state = state.1.control := by
  rfl

private lemma output_get (width : Nat) (field : Field) (first : Bool)
    (index : Fin (ScanMetadata.addressWidth width)) (state : Data width) :
    ((frame width field first).output.bit index).get state =
      state.2.1.getLsbD index.val := by
  change (addressBit width index.rev).get state = _
  rw [addressBit_get, BitVec.getMsbD_eq_getLsbD]
  have position : ScanMetadata.addressWidth width - 1 - index.rev.val = index.val := by
    simp only [Fin.val_rev]
    have within := index.isLt
    omega
  simp only [index.rev.isLt, decide_true, Bool.true_and, position]

/-- The independently defined first position reads the actual complete priority-ordered word. -/
lemma firstPosition_eq (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    (frame width field first).firstPosition state =
      NatFixedWidth.PriorityPrefix.firstOne (LengthAlignment.word width field first state) := by
  apply FirstOne.Frame.firstPosition_eq_firstOne
  intro index
  exact (LengthAlignment.word_get width field first state index).symm

/-- The literal native encoder XORs its full first position into the actual original address. -/
lemma address_read (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (state : Data width) (zero : state.2.2.1 = 0) :
    (GateSpec.stepList ((frame width field first).encoderGates height capacity fits)
      state).2.1 = state.2.1 ^^^ (if state.1.control then
        BitVec.ofNat (ScanMetadata.addressWidth width)
          (NatFixedWidth.PriorityPrefix.firstOne (LengthAlignment.word width field first state))
      else 0) := by
  have read := (frame width field first).encoderGates_read height capacity fits
    (fun value => value.2.1) (output_get width field first) state
    (clean_of_prefix_zero width field first state zero)
  rw [root_get, firstPosition_eq] at read
  exact read

/-- A clean enabled address contains the true natural first position, with an explicit fit bound. -/
lemma address_toNat (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (state : Data width) (zero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (enabled : state.1.control = true)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (GateSpec.stepList ((frame width field first).encoderGates height capacity fits)
      state).2.1.toNat =
        NatFixedWidth.PriorityPrefix.firstOne (LengthAlignment.word width field first state) := by
  have read := (frame width field first).encoderGates_read_toNat height capacity fits
    (fun value => value.2.1) (output_get width field first) state
    (clean_of_prefix_zero width field first state zero) addressZero enabled sentinelFits
  rw [firstPosition_eq] at read
  exact read

/-- Every physical original EEA source bit, including both full work words, is retained. -/
lemma source_get (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (state : Data width) (zero : state.2.2.1 = 0)
    (observed : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width observed).get
        (GateSpec.stepList ((frame width field first).encoderGates height capacity fits) state) =
      (sourceBit width observed).get state := by
  apply FirstOne.Frame.encoderGates_get_observed
    (clean := clean_of_prefix_zero width field first state zero)
  intro output
  exact (source_address_ne width observed output.rev).symm

/-- The complete existing prefix word returns to its original zero value. -/
lemma prefix_read (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (state : Data width) (zero : state.2.2.1 = 0) :
    (GateSpec.stepList ((frame width field first).encoderGates height capacity fits)
      state).2.2.1 = state.2.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have retained := (frame width field first).encoderGates_get_observed height capacity fits
    state (clean_of_prefix_zero width field first state zero) (prefixBit width ⟨index, within⟩)
    (fun output => address_prefix_ne width output.rev ⟨index, within⟩)
  simpa only [prefixBit_get] using retained

/-- The existing conjunction bit is retained without requiring its initial value to be clean. -/
lemma conjunction_get (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (state : Data width) (zero : state.2.2.1 = 0) :
    (conjunctionBit width).get
        (GateSpec.stepList ((frame width field first).encoderGates height capacity fits) state) =
      (conjunctionBit width).get state := by
  apply FirstOne.Frame.encoderGates_get_observed
    (clean := clean_of_prefix_zero width field first state zero)
  intro output
  exact address_conjunction_ne width output.rev

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder
