/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Frame

/-!
# First-one encoding on the existing terminal EEA systems

The complete original work word is read in static priority order. The
existing address is the arbitrary XOR output in least-significant-first
constant-write order. Original Ctrl and the complete prefix form the
actual retained traversal stack; original arbitrary Iter is restored work.
Every physical separation is independent of source values and trajectories.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma source_distinct (width : Nat) (field : Field) (first : Bool) :
    Function.Injective (fun index => ((LengthAlignment.source width field first).bit index).wire) :=
  by
  intro left right same
  have values := congrArg Fin.val same
  change (ArithmeticRotation.bit width first
      (LengthAlignment.priorityIndex width field left)).wire.val
      = (ArithmeticRotation.bit width first
        (LengthAlignment.priorityIndex width field right)).wire.val at values
  rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
  have positions : LengthAlignment.priorityIndex width field left =
      LengthAlignment.priorityIndex width field right := Fin.ext (by omega)
  cases field with
  | coefficient => exact Fin.rev_inj.mp positions
  | divisor => exact positions

private lemma source_before_metadata (width : Nat) (field : Field) (first : Bool)
    (index : Fin (width + 3)) :
    ((LengthAlignment.source width field first).bit index).wire.val < 2 * (width + 3) := by
  change (ArithmeticRotation.bit width first
      (LengthAlignment.priorityIndex width field index)).wire.val
    < _
  rw [ArithmeticRotation.bit_value]
  have within := (LengthAlignment.priorityIndex width field index).isLt
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

private lemma source_address (width : Nat) (field : Field) (first : Bool)
    (input : Fin (width + 3)) (output : Fin (ScanMetadata.addressWidth width)) :
    ((LengthAlignment.source width field first).bit input).wire ≠ (addressBit width output).wire :=
  by
  cases first <;> exact source_address_ne width _ output

private lemma source_prefix (width : Nat) (field : Field) (first : Bool)
    (input : Fin (width + 3)) (output : Fin (ScanMetadata.addressWidth width)) :
    ((LengthAlignment.source width field first).bit input).wire ≠ (prefixBit width output).wire :=
  by
  cases first <;> exact source_prefix_ne width _ output

private lemma source_flag (width : Nat) (field : Field) (first : Bool)
    (input : Fin (width + 3)) (original : EncodedBit (SharedEEA.encoding width))
    (afterWords : 2 * (width + 3) ≤ original.wire.val) :
    ((LengthAlignment.source width field first).bit input).wire ≠
      (sourceBit width original).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [sourceBit_wire] at values
  have before := source_before_metadata width field first input
  omega

private lemma stack_work (width : Nat) (index : Fin (ScanMetadata.addressWidth width + 1)) :
    (SelectionFrame.stack width index).wire ≠
      (sourceBit width (SharedEEA.iterationBit width)).wire := by
  unfold SelectionFrame.stack
  split
  · apply source_source_ne
    intro same
    have values := congrArg Fin.val same
    rw [SharedEEA.controlBit_wire, SharedEEA.iterationBit_wire] at values
    omega
  · exact (source_prefix_ne width _ _).symm

/-- Complete first-one frame borrows exactly the existing address, prefix and original Iter. -/
def frame (width : Nat) (field : Field) (first : Bool) :
    FirstOne.Frame (encoding width) (width + 3) (ScanMetadata.addressWidth width)
      (ScanMetadata.addressWidth width) where
  source := LengthAlignment.source width field first
  output := ⟨fun index => addressBit width index.rev⟩
  stack := ⟨SelectionFrame.stack width⟩
  work := sourceBit width (SharedEEA.iterationBit width)
  sourceDistinct := source_distinct width field first
  outputDistinct := by
    intro left right same
    apply Fin.rev_inj.mp
    by_contra different
    exact address_address_ne width left.rev right.rev different same
  stackDistinct := SelectionFrame.stack_distinct width
  sourceOutput := fun input output => source_address width field first input output.rev
  sourceStack := by
    intro input stackIndex
    unfold SelectionFrame.stack
    dsimp only
    split
    · exact source_flag width field first input (SharedEEA.controlBit width)
        (by rw [SharedEEA.controlBit_wire]; omega)
    · exact source_prefix width field first input _
  outputStack := fun output stackIndex => SelectionFrame.separate width output.rev stackIndex
  sourceWork := fun input => source_flag width field first input (SharedEEA.iterationBit width)
    (by rw [SharedEEA.iterationBit_wire]; omega)
  outputWork := fun output => (source_address_ne width _ output.rev).symm
  stackWork := stack_work width

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder
