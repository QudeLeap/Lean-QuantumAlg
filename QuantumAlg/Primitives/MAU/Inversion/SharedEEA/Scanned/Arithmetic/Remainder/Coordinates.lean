/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Wires
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Rotation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Placement
import all QuantumAlg.Util.Permutation.Rotation

/-!
# Identical remainder source positions after the complete paid alignment

The full static frame certifies positions only. Its displacement is the
original public proof coordinate of a window; the executed barrel reads
the actual quantum shift field. Both whole words, the arbitrary Sign,
every original complementary position and the entire shared pool remain
present [LYL+26, sec_EEA/sub_regshare.tex:263-278].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderCoordinates

noncomputable section

open EncodedBit

private lemma fits {width : Nat} (window : ArithmeticWindowRegisters.Window width) :
    window.length ≤ width + 3 := by
  have complete := window.complete
  omega

/-- The original complete remainder frame retains the whole existing shared pool. -/
def originalFrame {width : Nat} (window : ArithmeticWindowRegisters.Window width) :=
  (ArithmeticWindowPlacement.placement window).retainRight (poolEncoding width)

/-- The low native template follows the certified complete two-word alignment frame. -/
def templateFrame {width : Nat} (window : ArithmeticWindowRegisters.Window width) :=
  ((ArithmeticTop.placement width window.length (fits window)).full
    (ArithmeticTop.overflow_onto window.length) (Scanned.encoding_surjective width)).compose
      (ArithmeticAlignment.Fixed.frame width window.below)

private lemma template_prefix {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (index : Fin (Addition.TTK.overflowEncoding window.length).width) :
    (templateFrame window).mappedWire
        (Fin.castAdd (ArithmeticTop.placement width window.length (fits window)).complementWidth
          index) =
      (ArithmeticAlignment.Fixed.frame width window.below).mappedWire
        ((ArithmeticTop.placement width window.length (fits window)).wires index) := by
  have composition := FullPlacement.compose_mappedWire
    ((ArithmeticTop.placement width window.length (fits window)).full
      (ArithmeticTop.overflow_onto window.length) (Scanned.encoding_surjective width))
    (ArithmeticAlignment.Fixed.frame width window.below)
    (Fin.castAdd (ArithmeticTop.placement width window.length (fits window)).complementWidth index)
  exact composition.trans (congrArg
    (ArithmeticAlignment.Fixed.frame width window.below).mappedWire
    (CoefficientCoordinates.subsystem_prefix
      (ArithmeticTop.placement width window.length (fits window))
      (ArithmeticTop.overflow_onto window.length) (Scanned.encoding_surjective width) index))

private lemma original_prefix_value {width : Nat}
    (window : ArithmeticWindowRegisters.Window width)
    (index : Fin (Addition.TTK.overflowEncoding window.length).width) :
    ((originalFrame window).mappedWire
      (Fin.castAdd ((ArithmeticWindowEncoding.complementEncoding window).width +
        (poolEncoding width).width) index)).val =
      ArithmeticWindowCoordinates.physicalIndex window index.val := by
  have position := FullPlacement.retainRight_mappedWire_source
    (ArithmeticWindowPlacement.placement window) (poolEncoding width) index
  have value := congrArg Fin.val position
  have original : ((ArithmeticWindowPlacement.placement window).mappedWire
      (Fin.castAdd (ArithmeticWindowEncoding.complementEncoding window).width index)).val =
        ArithmeticWindowCoordinates.physicalIndex window index.val := by
    change FullPlacement.wireAddress _ _ (ArithmeticWindowFullCoordinates.wireEquiv window)
      (Fin.castAdd (ArithmeticWindowEncoding.complementEncoding window).width index).val = _
    have within : index.val < 2 * window.length + 1 := by
      have bound := index.isLt
      change index.val < window.length + window.length + 1 at bound
      omega
    exact (dif_pos (Fin.isLt _)).trans
      (ArithmeticWindowFullCoordinates.physicalIndex_focus window ⟨index.val, within⟩)
  exact value.trans original

private lemma rotated_index {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (index : Fin window.length) :
    ((ArithmeticAlignment.permutation width ^ window.below)
      (ArithmeticTemplate.littleIndex width
        (ArithmeticWindow.lowIndex width window.length (fits window) index))).val =
      window.above + index.val := by
  have : NeZero (width + 3) := ⟨by omega⟩
  have below : window.below ≤
      (ArithmeticTemplate.littleIndex width
        (ArithmeticWindow.lowIndex width window.length (fits window) index)).val := by
    change window.below ≤ width + 3 - 1 - (window.length - 1 - index.val)
    have complete := window.complete
    have within := index.isLt
    omega
  have moved := Permutation.inverseRotation_pow_apply_of_le window.below
    (ArithmeticTemplate.littleIndex width
      (ArithmeticWindow.lowIndex width window.length (fits window) index)) below
  change (((finRotate (width + 3))⁻¹ ^ window.below) _).val = _
  rw [moved]
  change width + 3 - 1 - (window.length - 1 - index.val) - window.below = _
  have complete := window.complete
  have within := index.isLt
  omega

private lemma template_operand_value {width : Nat}
    (window : ArithmeticWindowRegisters.Window width) (first : Bool)
    (index : Fin window.length) :
    ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire
      (ArithmeticTemplate.wordBit width first
        (ArithmeticWindow.lowIndex width window.length (fits window) index)).wire).val =
      (if first then 0 else width + 3) + (window.above + index.val) := by
  change ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire
    (ArithmeticRotation.bit width first (ArithmeticTemplate.littleIndex width
      (ArithmeticWindow.lowIndex width window.length (fits window) index))).wire).val = _
  rw [ArithmeticAlignment.Fixed.frame_mapped_word, ArithmeticRotation.bit_value, rotated_index]

private lemma template_sign_fixed {width : Nat} (window : ArithmeticWindowRegisters.Window width) :
    (ArithmeticAlignment.Fixed.frame width window.below).mappedWire
        (ArithmeticTop.sign width).wire = (ArithmeticTop.sign width).wire := by
  apply ArithmeticAlignment.Fixed.frame_mapped_other
  rw [ArithmeticAlignment.Fixed.operands_range_iff]
  have source := (sourceBit_wire width (SharedEEA.signBit width)).trans
    (SharedEEA.signBit_wire width)
  change (ArithmeticTop.sign width).wire.val = 2 * (width + 3) + 4 * width.size + 2 at source
  rw [source]
  omega

/-- Every overflow input and Sign output is the same literal original physical source position. -/
lemma source_positions {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (index : Fin (Addition.TTK.overflowEncoding window.length).width) :
    (templateFrame window).mappedWire
        (Fin.castAdd (ArithmeticTop.placement width window.length (fits window)).complementWidth
          index) =
      (originalFrame window).mappedWire
        (Fin.castAdd ((ArithmeticWindowEncoding.complementEncoding window).width +
          (poolEncoding width).width) index) := by
  apply Fin.ext
  rw [template_prefix, original_prefix_value]
  refine Fin.addCases (m := (Addition.TTK.encoding window.length).width) (n := 1)
    (fun operands => ?_) (fun output => ?_) index
  · rw [CoefficientCoordinates.top_source_wire]
    refine Fin.addCases (m := window.length) (n := window.length)
      (fun left => ?_) (fun right => ?_) operands
    · change ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire
        ((wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd window.length left))).val = _
      rw [wordPairSubsystem_left]
      change ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire
        (ArithmeticTemplate.wordBit width false
          (ArithmeticWindow.lowIndex width window.length (fits window) left)).wire).val =
        ArithmeticWindowCoordinates.physicalIndex window left.val
      rw [template_operand_value]
      simp only [Bool.false_eq_true, if_false]
      rw [ArithmeticWindowCoordinates.physicalIndex, if_pos left.isLt]
      omega
    · change ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire
        ((wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd window.length right))).val = _
      rw [wordPairSubsystem_right]
      change ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire
        (ArithmeticTemplate.wordBit width true
          (ArithmeticWindow.lowIndex width window.length (fits window) right)).wire).val =
        ArithmeticWindowCoordinates.physicalIndex window (window.length + right.val)
      rw [template_operand_value]
      simp only [if_true, zero_add]
      have initial : ¬window.length + right.val < window.length := by omega
      have second : window.length + right.val < 2 * window.length := by
        have within := right.isLt
        omega
      rw [ArithmeticWindowCoordinates.physicalIndex, if_neg initial, if_pos second,
        Nat.add_sub_cancel_left]
  · have zero : output = (0 : Fin 1) := by
      apply Fin.ext
      have within := output.isLt
      change output.val < 1 at within
      omega
    subst output
    have value := congrArg (fun position : Fin (encoding width).width =>
      ((ArithmeticAlignment.Fixed.frame width window.below).mappedWire position).val)
      (CoefficientCoordinates.top_flag_wire width window.length (fits window))
    have fixed := congrArg Fin.val (template_sign_fixed window)
    have original := ArithmeticWindowCoordinates.physicalIndex_sign window
    exact value.trans (fixed.trans original.symm)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderCoordinates
