/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Rotation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Encoding
import all QuantumAlg.Primitives.MAU.Addition.TTK.Layout
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Compose
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Retain
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag
import all QuantumAlg.Components.Encoded.BitGates.StateEquality

/-!
# Identical original coefficient source positions beside the complete shared pool

The literal overflow source prefix of the statically placed streamed
template is exactly the original coefficient-window prefix. The original
saved frame and the entire existing pool remain explicit complements.
This source-position certificate supplies no executed arithmetic gate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientCoordinates

noncomputable section

open EncodedBit

/-- The original coefficient arithmetic starts at physical little-endian position zero. -/
@[implicit_reducible] def window (width length : Nat) (fits : length ≤ width + 3) :
    ArithmeticWindowRegisters.Window width where
  above := 0
  length := length
  below := width + 3 - length
  complete := by omega

/-- The original complete coefficient frame explicitly retains the whole existing shared pool. -/
def originalFrame (width length : Nat) (fits : length ≤ width + 3) :=
  (CoefficientWindowProgram.placement (window width length fits)).retainRight (poolEncoding width)

/-- The actual template source positions pass through the same static coefficient placement. -/
def templateFrame (width length : Nat) (fits : length ≤ width + 3) :=
  ((ArithmeticTop.placement width length fits).full (ArithmeticTop.overflow_onto length)
    (Scanned.encoding_surjective width)).compose (CoefficientFrame.placement width)

private lemma subsystem_prefix {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (subsystem : WireSubsystem source target)
    (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (index : Fin source.width) :
    (subsystem.full sourceOnto targetOnto).mappedWire
        (Fin.castAdd subsystem.complementWidth index) = subsystem.wires index := by
  have actual := subsystem.placeBit_wire sourceOnto targetOnto (fullBit sourceOnto index)
  exact actual

private lemma template_prefix (width length : Nat) (fits : length ≤ width + 3)
    (index : Fin (Addition.TTK.overflowEncoding length).width) :
    (templateFrame width length fits).mappedWire
        (Fin.castAdd (ArithmeticTop.placement width length fits).complementWidth index) =
      (CoefficientFrame.placement width).mappedWire
        ((ArithmeticTop.placement width length fits).wires index) := by
  have composition := FullPlacement.compose_mappedWire
    ((ArithmeticTop.placement width length fits).full (ArithmeticTop.overflow_onto length)
      (Scanned.encoding_surjective width)) (CoefficientFrame.placement width)
    (Fin.castAdd (ArithmeticTop.placement width length fits).complementWidth index)
  exact composition.trans (congrArg (CoefficientFrame.placement width).mappedWire
    (subsystem_prefix (ArithmeticTop.placement width length fits)
      (ArithmeticTop.overflow_onto length) (Scanned.encoding_surjective width) index))

private lemma original_prefix_value (width length : Nat) (fits : length ≤ width + 3)
    (index : Fin (Addition.TTK.overflowEncoding length).width) :
    ((originalFrame width length fits).mappedWire
      (Fin.castAdd ((ArithmeticWindowEncoding.complementEncoding
        (window width length fits)).width + (poolEncoding width).width) index)).val =
      CoefficientWindowCoordinates.physicalIndex (window width length fits) index.val := by
  have position := FullPlacement.retainRight_mappedWire_source
    (CoefficientWindowProgram.placement (window width length fits)) (poolEncoding width) index
  have value := congrArg Fin.val position
  have original : ((CoefficientWindowProgram.placement (window width length fits)).mappedWire
      (Fin.castAdd (ArithmeticWindowEncoding.complementEncoding
        (window width length fits)).width index)).val =
        CoefficientWindowCoordinates.physicalIndex (window width length fits) index.val := by
    change FullPlacement.wireAddress _ _
      (CoefficientWindowCoordinates.wireEquiv (window width length fits))
      (Fin.castAdd (ArithmeticWindowEncoding.complementEncoding
        (window width length fits)).width index).val = _
    exact (dif_pos (Fin.isLt _)).trans rfl
  exact value.trans original

private lemma template_operand_value (width length : Nat) (fits : length ≤ width + 3)
    (first : Bool) (index : Fin length) :
    ((CoefficientFrame.placement width).mappedWire
      (ArithmeticTemplate.wordBit width first
        (ArithmeticWindow.lowIndex width length fits index)).wire).val =
      (if first then width + 3 else 0) + (length - 1 - index.val) := by
  have placed := congrArg (fun bit : EncodedBit (encoding width) => bit.wire.val)
    (CoefficientFrame.placed_wordBit width first
      (ArithmeticWindow.lowIndex width length fits index))
  change _ = (ArithmeticRotation.bit width (!first)
    (ArithmeticWindow.lowIndex width length fits index)).wire.val at placed
  rw [ArithmeticRotation.bit_value] at placed
  cases first <;>
    simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
      ArithmeticWindow.lowIndex, FullPlacement.placeBit] using placed

private lemma top_source_wire (width length : Nat) (fits : length ≤ width + 3)
    (index : Fin (Addition.TTK.encoding length).width) :
    (ArithmeticTop.placement width length fits).wires (Fin.castAdd 1 index) =
      (ArithmeticWindow.placement width length fits).subsystem.wires index :=
  (ArithmeticWindow.placement width length fits).subsystem.withFlag_source
    (ArithmeticTop.sign width) (ArithmeticTop.subsystem_sign_ne width length fits) index

private lemma top_flag_wire (width length : Nat) (fits : length ≤ width + 3) :
    (ArithmeticTop.placement width length fits).wires
      (Fin.natAdd (Addition.TTK.encoding length).width (0 : Fin 1)) =
        (ArithmeticTop.sign width).wire :=
  (ArithmeticWindow.placement width length fits).subsystem.withFlag_flag
    (ArithmeticTop.sign width) (ArithmeticTop.subsystem_sign_ne width length fits)

/-- Every overflow source position is literally the original coefficient position. -/
lemma source_positions (width length : Nat) (fits : length ≤ width + 3)
    (index : Fin (Addition.TTK.overflowEncoding length).width) :
    (templateFrame width length fits).mappedWire
        (Fin.castAdd (ArithmeticTop.placement width length fits).complementWidth index) =
      (originalFrame width length fits).mappedWire
        (Fin.castAdd ((ArithmeticWindowEncoding.complementEncoding
          (window width length fits)).width + (poolEncoding width).width) index) := by
  apply Fin.ext
  rw [template_prefix, original_prefix_value]
  refine Fin.addCases (m := (Addition.TTK.encoding length).width) (n := 1)
    (fun operands => ?_) (fun output => ?_) index
  · rw [top_source_wire]
    refine Fin.addCases (m := length) (n := length)
      (fun left => ?_) (fun right => ?_) operands
    · change ((CoefficientFrame.placement width).mappedWire
        ((wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd length left))).val = _
      rw [wordPairSubsystem_left]
      change ((CoefficientFrame.placement width).mappedWire
        (ArithmeticTemplate.wordBit width false
          (ArithmeticWindow.lowIndex width length fits left)).wire).val = _
      rw [template_operand_value]
      simp only [Bool.false_eq_true, if_false, zero_add]
      change length - 1 - left.val =
        CoefficientWindowCoordinates.physicalIndex (window width length fits) left.val
      have reflected : length - 1 - left.rev.val = left.val := by
        rw [Fin.val_rev]
        have within := left.isLt
        omega
      have reversed : left.rev.val = length - 1 - left.val := by
        rw [Fin.val_rev]
        omega
      have original :=
        CoefficientWindowCoordinates.physicalIndex_source (window width length fits) left.rev
      have position :
          CoefficientWindowCoordinates.physicalIndex (window width length fits) left.val =
            left.rev.val := by
        simpa only [window, reflected, zero_add] using original
      exact (position.trans reversed).symm
    · change ((CoefficientFrame.placement width).mappedWire
        ((wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd length right))).val = _
      rw [wordPairSubsystem_right]
      change ((CoefficientFrame.placement width).mappedWire
        (ArithmeticTemplate.wordBit width true
          (ArithmeticWindow.lowIndex width length fits right)).wire).val = _
      rw [template_operand_value]
      change width + 3 + (length - 1 - right.val) =
        CoefficientWindowCoordinates.physicalIndex (window width length fits) (length + right.val)
      have reflected : length - 1 - right.rev.val = right.val := by
        rw [Fin.val_rev]
        have within := right.isLt
        omega
      have reversed : right.rev.val = length - 1 - right.val := by
        rw [Fin.val_rev]
        omega
      have original :=
        CoefficientWindowCoordinates.physicalIndex_target (window width length fits) right.rev
      have position :
          CoefficientWindowCoordinates.physicalIndex
            (window width length fits) (length + right.val) =
            width + 3 + right.rev.val := by
        simpa only [window, reflected, Nat.add_zero] using original
      exact (position.trans (congrArg (fun value => width + 3 + value) reversed)).symm
  · have zero : output = (0 : Fin 1) := by
      apply Fin.ext
      change output.val = 0
      have within := output.isLt
      change output.val < 1 at within
      omega
    subst output
    have value := congrArg
      (fun position : Fin (encoding width).width =>
        ((CoefficientFrame.placement width).mappedWire position).val)
      (top_flag_wire width length fits)
    have fixed : ((CoefficientFrame.placement width).mappedWire
        (ArithmeticTop.sign width).wire).val = (SharedEEA.signBit width).wire.val := by
      have source := (sourceBit_wire width (SharedEEA.signBit width)).trans
        (SharedEEA.signBit_wire width)
      change (ArithmeticTop.sign width).wire.val =
        2 * (width + 3) + 4 * width.size + 2 at source
      have original := CoefficientFrame.wires_retained width (ArithmeticTop.sign width).wire (by
        omega)
      change FullPlacement.wireAddress (encoding width) (encoding width)
        (CoefficientFrame.wires width) (ArithmeticTop.sign width).wire.val = _
      exact (dif_pos (ArithmeticTop.sign width).wire.isLt).trans (congrArg Fin.val original)
    have original := CoefficientWindowCoordinates.physicalIndex_sign (window width length fits)
    have final : (SharedEEA.signBit width).wire.val =
        CoefficientWindowCoordinates.physicalIndex (window width length fits)
          (Fin.natAdd (Addition.TTK.encoding length).width (0 : Fin 1)).val := by
      simpa only [window, Fin.val_natAdd, Fin.val_zero, Nat.add_zero,
        Addition.TTK.ttkEncoding_width]
        using original.symm
    exact value.trans (fixed.trans final)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientCoordinates
