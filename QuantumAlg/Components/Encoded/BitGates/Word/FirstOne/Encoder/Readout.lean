/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Correctness

/-!
# Exact arbitrary-output XOR and nontruncated numeric first-one readout

The bitwise XOR theorem admits every output and every width. The separate
natural-number readout explicitly requires the full count sentinel to fit.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Every actual output bit XORs the same original enabled first-position word. -/
lemma encoderGates_output_get (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (state : Data) (clean : frame.CleanFrom 0 state)
    (index : Fin outputWidth) :
    (frame.output.bit index).get
        (GateSpec.stepList (frame.encoderGates height capacity fits) state) =
      ((frame.output.bit index).get state ^^ ((frame.stack.bit ⟨0, by omega⟩).get state &&
        (BitVec.ofNat outputWidth (frame.firstPosition state)).getLsbD index.val)) := by
  rw [frame.encoderGates_step height capacity fits state clean]
  cases selected : (frame.stack.bit ⟨0, by omega⟩).get state
  · simp only [Bool.false_eq_true, if_false, Bool.false_and, Bool.xor_false]
  · simp only [if_true, Bool.true_and]
    exact Word.xorConstantStep_get_target frame.output _ index
      (fun other different => fun same => different (frame.outputDistinct same)) state

/-- Every physical read outside the supplied output word retains its exact original value. -/
lemma encoderGates_get_observed (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (state : Data) (clean : frame.CleanFrom 0 state)
    (observed : EncodedBit encoding)
    (outside : ∀ output, (frame.output.bit output).wire ≠ observed.wire) :
    observed.get (GateSpec.stepList (frame.encoderGates height capacity fits) state) =
      observed.get state := by
  rw [frame.encoderGates_step height capacity fits state clean]
  split
  · exact Word.xorConstantStep_get_observed_of_target_ne _ _ _ outside state
  · rfl

/-- Any correctly placed complete output-word readout sees the exact enabled XOR word. -/
lemma encoderGates_read (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (read : Data → BitVec outputWidth)
    (reads : ∀ index state, (frame.output.bit index).get state = (read state).getLsbD index.val)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    read (GateSpec.stepList (frame.encoderGates height capacity fits) state) =
      read state ^^^ (if (frame.stack.bit ⟨0, by omega⟩).get state then
        BitVec.ofNat outputWidth (frame.firstPosition state) else 0) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index bounded
  rw [← reads ⟨index, bounded⟩, frame.encoderGates_output_get height capacity fits state clean,
    reads, BitVec.getLsbD_xor]
  cases (frame.stack.bit ⟨0, by omega⟩).get state <;>
    simp only [Bool.false_eq_true, if_false, Bool.false_and, BitVec.ofNat_eq_ofNat,
      BitVec.getLsbD_zero,
      if_true, Bool.true_and]

/-- A clean enabled output has the true natural first position when the full sentinel fits. -/
lemma encoderGates_read_toNat (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (read : Data → BitVec outputWidth)
    (reads : ∀ index state, (frame.output.bit index).get state = (read state).getLsbD index.val)
    (state : Data) (clean : frame.CleanFrom 0 state) (outputZero : read state = 0)
    (enabled : (frame.stack.bit ⟨0, by omega⟩).get state = true)
    (sentinelFits : count < 2 ^ outputWidth) :
    (read (GateSpec.stepList (frame.encoderGates height capacity fits) state)).toNat =
      frame.firstPosition state := by
  rw [frame.encoderGates_read height capacity fits read reads state clean, outputZero, enabled]
  simp only [if_true, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (ListPriority.Tree.position_le _) sentinelFits)

end

end QuantumAlg.EncodedBit.FirstOne.Frame
