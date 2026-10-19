/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.FullCoordinates
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

/-!
# Place the actual grouped-window native program on the original frame

The complete grouped body may use both operand windows, Sign, and the
existing complementary control/work bits. Its basis map is induced by
the explicit bijection of every grouped wire with an original frame wire.
No mathematical arithmetic permutation is declared as a gate, and the
body supplies its actual native program and its own realization proof
[LYL+26, sec_EEA/sub_regshare.tex:16-26,263-278].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowPlacement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ArithmeticWindowRegisters ArithmeticWindowEncoding ArithmeticWindowFullCoordinates

/-- The complete semantic basis transport is induced by the proved native wire bijection. -/
def placement {width : Nat} (window : Window width) :
    EncodedBit.FullPlacement (groupedEncoding window) (encoding width) :=
  EncodedBit.FullPlacement.ofWires (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)

private def focusBit {width : Nat} (window : Window width)
    (bit : EncodedBit (Addition.TTK.overflowEncoding window.length)) :
    EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodLeftBit _ _ bit

private lemma focus_wire {width : Nat} (window : Window width)
    (bit : EncodedBit (Addition.TTK.overflowEncoding window.length)) :
    (focusBit window bit).wire.val = bit.wire.val := rfl

/-- The native TTK source lens reads the actual Work2 window through the strict placement. -/
lemma source_read {width : Nat} (window : Window width)
    (index : Fin window.length) (state : Registers width) :
    (focusBit window
      (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index))).get
        ((placement window).grouping state) = (sourceBit window index).get state := by
  let bit := focusBit window
    (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index))
  have same : wireEquiv window bit.wire = (sourceBit window index).wire := by
    apply Fin.ext
    change physicalIndex window bit.wire.val = (sourceBit window index).wire.val
    rw [focus_wire window]
    have within :
        (Addition.TTK.withOverflowBit
          (Addition.TTK.leftBit window.length index)).wire.val <
            2 * window.length + 1 := by
      simpa only [Addition.TTK.ttkOverflowEncoding_width] using
        (Addition.TTK.withOverflowBit
          (Addition.TTK.leftBit window.length index)).wire.isLt
    exact (physicalIndex_focus window ⟨_, within⟩).trans
      (ArithmeticWindowCoordinates.physicalIndex_source window index)
  exact EncodedBit.FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    bit (sourceBit window index) same state

/-- The native TTK target lens reads the actual Work1 window through the strict placement. -/
lemma target_read {width : Nat} (window : Window width)
    (index : Fin window.length) (state : Registers width) :
    (focusBit window
      (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index))).get
        ((placement window).grouping state) = (targetBit window index).get state := by
  let bit := focusBit window
    (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index))
  have same : wireEquiv window bit.wire = (targetBit window index).wire := by
    apply Fin.ext
    change physicalIndex window bit.wire.val = (targetBit window index).wire.val
    rw [focus_wire window]
    have within :
        (Addition.TTK.withOverflowBit
          (Addition.TTK.rightBit window.length index)).wire.val <
            2 * window.length + 1 := by
      simpa only [Addition.TTK.ttkOverflowEncoding_width] using
        (Addition.TTK.withOverflowBit
          (Addition.TTK.rightBit window.length index)).wire.isLt
    exact (physicalIndex_focus window ⟨_, within⟩).trans
      (ArithmeticWindowCoordinates.physicalIndex_target window index)
  exact EncodedBit.FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    bit (targetBit window index) same state

/-- The TTK overflow bit reads the original Sign wire through the strict placement. -/
lemma sign_read {width : Nat} (window : Window width) (state : Registers width) :
    (focusBit window (Addition.TTK.overflowBit window.length)).get
        ((placement window).grouping state) = (signBit width).get state := by
  let bit := focusBit window (Addition.TTK.overflowBit window.length)
  have same : wireEquiv window bit.wire = (signBit width).wire := by
    apply Fin.ext
    change physicalIndex window bit.wire.val = (signBit width).wire.val
    rw [focus_wire window]
    have within : (Addition.TTK.overflowBit window.length).wire.val <
        2 * window.length + 1 := by
      simpa only [Addition.TTK.ttkOverflowEncoding_width] using
        (Addition.TTK.overflowBit window.length).wire.isLt
    exact (physicalIndex_focus window ⟨_, within⟩).trans
      (ArithmeticWindowCoordinates.physicalIndex_sign window)
  exact EncodedBit.FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    bit (signBit width) same state

/-- The derived placement and source grouping agree on every TTK source bit. -/
lemma source_grouping {width : Nat} (window : Window width)
    (index : Fin window.length) (state : Registers width) :
    (focusBit window
      (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index))).get
        ((placement window).grouping state) =
      (focusBit window
        (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index))).get
          (grouping window state) :=
  (source_read window index state).trans
    (ArithmeticWindowRegisters.grouping_source_bit window index state).symm

/-- The derived placement and source grouping agree on every TTK target bit. -/
lemma target_grouping {width : Nat} (window : Window width)
    (index : Fin window.length) (state : Registers width) :
    (focusBit window
      (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index))).get
        ((placement window).grouping state) =
      (focusBit window
        (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index))).get
          (grouping window state) :=
  (target_read window index state).trans
    (ArithmeticWindowRegisters.grouping_target_bit window index state).symm

/-- The derived placement and source grouping agree on the exact Sign output. -/
lemma sign_grouping {width : Nat} (window : Window width) (state : Registers width) :
    (focusBit window (Addition.TTK.overflowBit window.length)).get
        ((placement window).grouping state) =
      (focusBit window (Addition.TTK.overflowBit window.length)).get
        (grouping window state) := by
  rw [sign_read, signBit_get]
  rfl

/-- The original Ctrl is read at its unchanged source address. -/
lemma control_read {width : Nat} (window : Window width) (state : Registers width) :
    (ArithmeticWindowEncoding.controlBit window).get
      ((placement window).grouping state) = (SharedEEA.controlBit width).get state := by
  have same : wireEquiv window (ArithmeticWindowEncoding.controlBit window).wire =
      (SharedEEA.controlBit width).wire := by
    apply Fin.ext
    exact physicalIndex_control window
  exact EncodedBit.FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (ArithmeticWindowEncoding.controlBit window) (SharedEEA.controlBit width) same state

/-- The arbitrary Iter bit is read at its retained original source address. -/
lemma work_read {width : Nat} (window : Window width) (state : Registers width) :
    (ArithmeticWindowEncoding.workBit window).get
      ((placement window).grouping state) = (iterationBit width).get state := by
  have same : wireEquiv window (ArithmeticWindowEncoding.workBit window).wire =
      (iterationBit width).wire := by
    apply Fin.ext
    exact physicalIndex_work window
  exact EncodedBit.FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (ArithmeticWindowEncoding.workBit window) (iterationBit width) same state

/-- Both groupings agree on the original Ctrl without any preparation assumption. -/
lemma control_grouping {width : Nat} (window : Window width) (state : Registers width) :
    (ArithmeticWindowEncoding.controlBit window).get
      ((placement window).grouping state) =
        (ArithmeticWindowEncoding.controlBit window).get (grouping window state) := by
  rw [control_read, SharedEEA.controlBit_get, ArithmeticWindowEncoding.controlBit_get]

/-- Both groupings agree on the arbitrary borrowed Iter work bit. -/
lemma work_grouping {width : Nat} (window : Window width) (state : Registers width) :
    (ArithmeticWindowEncoding.workBit window).get
      ((placement window).grouping state) =
        (ArithmeticWindowEncoding.workBit window).get (grouping window state) := by
  rw [work_read, iterationBit_get, ArithmeticWindowEncoding.workBit_get]

/-- The complete TTK source, target and overflow focus matches the registered grouping. -/
lemma focus_grouping {width : Nat} (window : Window width) (state : Registers width) :
    ((placement window).grouping state).1 = (grouping window state).1 := by
  apply Prod.ext
  · apply Prod.ext
    · apply (BinaryBasis.bigEndianEquiv window.length).symm.injective
      funext index
      apply finTwoEquiv.injective
      simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
      have actual := source_grouping window index.rev state
      change (Addition.TTK.withOverflowBit
        (Addition.TTK.leftBit window.length index.rev)).get
          ((placement window).grouping state).1 =
        (Addition.TTK.withOverflowBit
          (Addition.TTK.leftBit window.length index.rev)).get
            (grouping window state).1 at actual
      rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkWithOverflowBit_get,
        Addition.TTK.ttkLeftBit_get, Addition.TTK.ttkLeftBit_get] at actual
      exact actual
    · apply (BinaryBasis.bigEndianEquiv window.length).symm.injective
      funext index
      apply finTwoEquiv.injective
      simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
      have actual := target_grouping window index.rev state
      change (Addition.TTK.withOverflowBit
        (Addition.TTK.rightBit window.length index.rev)).get
          ((placement window).grouping state).1 =
        (Addition.TTK.withOverflowBit
          (Addition.TTK.rightBit window.length index.rev)).get
            (grouping window state).1 at actual
      rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkWithOverflowBit_get,
        Addition.TTK.ttkRightBit_get, Addition.TTK.ttkRightBit_get] at actual
      exact actual
  · exact sign_grouping window state

/-- Lift a bit of the first retained pair of length words through the complete grouped frame. -/
private def firstLengthsBit {width : Nat} (window : Window width)
    (bit : EncodedBit (lengthPairEncoding width)) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodLeftBit _ _ bit)))

private def coefficientBit {width : Nat} (window : Window width)
    (index : Fin width.size) : EncodedBit (groupedEncoding window) :=
  firstLengthsBit window
    (BinaryLabelEncoding.prodLeftBit _ _ (wordBit index))

private lemma coefficientBit_wire {width : Nat} (window : Window width)
    (index : Fin width.size) :
    (coefficientBit window index).wire.val =
      (window.length + window.length + 1) +
        ((window.above + window.below) + (window.above + window.below) + index.val) := by
  simp only [coefficientBit, firstLengthsBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightWire_val,
    BinaryLabelEncoding.prodLeftWire_val]
  change (window.length + window.length + 1) +
    ((window.above + window.below) +
      ((window.above + window.below) + index.val)) = _
  omega

/-- The first grouped length field reads the original coefficient-length wire. -/
lemma coefficient_read {width : Nat} (window : Window width)
    (index : Fin width.size) (state : Registers width) :
    (coefficientBit window index).get ((placement window).grouping state) =
      (coefficientLengthBit width index).get state := by
  have same : wireEquiv window (coefficientBit window index).wire =
      (coefficientLengthBit width index).wire := by
    apply Fin.ext
    change physicalIndex window (coefficientBit window index).wire.val =
      (coefficientLengthBit width index).wire.val
    rw [coefficientBit_wire, coefficientLengthBit_wire]
    have complete := window.complete
    have within := index.isLt
    unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
    split_ifs <;> omega
  exact EncodedBit.FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (coefficientBit window index) (coefficientLengthBit width index) same state

/-- The first grouped length field agrees bitwise with the original field grouping. -/
lemma coefficient_grouping {width : Nat} (window : Window width)
    (index : Fin width.size) (state : Registers width) :
    (coefficientBit window index).get ((placement window).grouping state) =
      (coefficientBit window index).get (grouping window state) := by
  rw [coefficient_read, coefficientLengthBit_get]
  change state.coefficientLength.getMsbD index.val =
    (wordBit index).get state.coefficientLength
  exact (wordBit_get index state.coefficientLength).symm

/-- The coefficient-length word is retained exactly by the physical placement. -/
lemma coefficient_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.2.1.1 =
      (grouping window state).2.2.2.1.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin width.size := ⟨index, within⟩
  have actual := coefficient_grouping window selected state
  change (wordBit selected).get ((placement window).grouping state).2.2.2.1.1 =
    (wordBit selected).get (grouping window state).2.2.2.1.1 at actual
  simpa only [wordBit_get] using actual

private def quotientBit {width : Nat} (window : Window width)
    (index : Fin width.size) : EncodedBit (groupedEncoding window) :=
  firstLengthsBit window
    (BinaryLabelEncoding.prodRightBit _ _ (wordBit index))

private lemma quotientBit_wire {width : Nat} (window : Window width)
    (index : Fin width.size) :
    (quotientBit window index).wire.val =
      (window.length + window.length + 1) +
        (2 * (window.above + window.below) + width.size + index.val) := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) +
      ((window.above + window.below) + (width.size + index.val))) = _
  omega

/-- The quotient-length word is retained exactly by the physical placement. -/
lemma quotient_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.2.1.2 =
      (grouping window state).2.2.2.1.2 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin width.size := ⟨index, within⟩
  have same : wireEquiv window (quotientBit window selected).wire =
      (quotientLengthBit width selected).wire := by
    apply Fin.ext
    change physicalIndex window (quotientBit window selected).wire.val =
      (quotientLengthBit width selected).wire.val
    rw [quotientBit_wire, quotientLengthBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (quotientBit window selected) (quotientLengthBit width selected) same state
  change (wordBit selected).get ((placement window).grouping state).2.2.2.1.2 =
    (quotientLengthBit width selected).get state at actual
  rw [wordBit_get, quotientLengthBit_get] at actual
  exact actual

private def secondLengthsBit {width : Nat} (window : Window width)
    (bit : EncodedBit (lengthPairEncoding width)) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodRightBit _ _
          (BinaryLabelEncoding.prodLeftBit _ _ bit))))

private def divisorBit {width : Nat} (window : Window width)
    (index : Fin width.size) : EncodedBit (groupedEncoding window) :=
  secondLengthsBit window (BinaryLabelEncoding.prodLeftBit _ _ (wordBit index))

private lemma divisorBit_wire {width : Nat} (window : Window width)
    (index : Fin width.size) :
    (divisorBit window index).wire.val =
      (window.length + window.length + 1) +
        (2 * (window.above + window.below) + 2 * width.size + index.val) := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) +
      ((window.above + window.below) + ((width.size + width.size) + index.val))) = _
  omega

/-- The divisor-length word is retained exactly by the physical placement. -/
lemma divisor_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.2.2.1.1 =
      (grouping window state).2.2.2.2.1.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin width.size := ⟨index, within⟩
  have same : wireEquiv window (divisorBit window selected).wire =
      (divisorLengthBit width selected).wire := by
    apply Fin.ext
    change physicalIndex window (divisorBit window selected).wire.val =
      (divisorLengthBit width selected).wire.val
    rw [divisorBit_wire, divisorLengthBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (divisorBit window selected) (divisorLengthBit width selected) same state
  change (wordBit selected).get ((placement window).grouping state).2.2.2.2.1.1 =
    (divisorLengthBit width selected).get state at actual
  rw [wordBit_get, divisorLengthBit_get] at actual
  exact actual

private def shiftBit {width : Nat} (window : Window width)
    (index : Fin width.size) : EncodedBit (groupedEncoding window) :=
  secondLengthsBit window (BinaryLabelEncoding.prodRightBit _ _ (wordBit index))

private lemma shiftBit_wire {width : Nat} (window : Window width)
    (index : Fin width.size) :
    (shiftBit window index).wire.val =
      (window.length + window.length + 1) +
        (2 * (window.above + window.below) + 3 * width.size + index.val) := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) +
      ((window.above + window.below) +
        ((width.size + width.size) + (width.size + index.val)))) = _
  omega

/-- The shift word is retained exactly by the physical placement. -/
lemma shift_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.2.2.1.2 =
      (grouping window state).2.2.2.2.1.2 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin width.size := ⟨index, within⟩
  have same : wireEquiv window (shiftBit window selected).wire =
      (SharedEEA.shiftBit width selected).wire := by
    apply Fin.ext
    change physicalIndex window (shiftBit window selected).wire.val =
      (SharedEEA.shiftBit width selected).wire.val
    rw [shiftBit_wire, SharedEEA.shiftBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (shiftBit window selected) (SharedEEA.shiftBit width selected) same state
  change (wordBit selected).get ((placement window).grouping state).2.2.2.2.1.2 =
    (SharedEEA.shiftBit width selected).get state at actual
  rw [wordBit_get, SharedEEA.shiftBit_get] at actual
  exact actual

private def retainedFlagBit {width : Nat} (window : Window width)
    (bit : EncodedBit flagEncoding) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodRightBit _ _
          (BinaryLabelEncoding.prodRightBit _ _ bit))))

private def firstPhaseBit {width : Nat} (window : Window width) :
    EncodedBit (groupedEncoding window) :=
  retainedFlagBit window
    (BinaryLabelEncoding.prodLeftBit _ _
      (BinaryLabelEncoding.prodLeftBit _ _ BinaryLabelEncoding.boolBit))

private lemma firstPhaseBit_wire {width : Nat} (window : Window width) :
    (firstPhaseBit window).wire.val =
      2 * window.length + 1 + 2 * (window.above + window.below) +
        4 * width.size := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) +
      ((window.above + window.below) +
        ((width.size + width.size) + ((width.size + width.size) + 0)))) = _
  omega

private def secondPhaseBit {width : Nat} (window : Window width) :
    EncodedBit (groupedEncoding window) :=
  retainedFlagBit window
    (BinaryLabelEncoding.prodLeftBit _ _
      (BinaryLabelEncoding.prodRightBit _ _ BinaryLabelEncoding.boolBit))

private lemma secondPhaseBit_wire {width : Nat} (window : Window width) :
    (secondPhaseBit window).wire.val =
      2 * window.length + 1 + 2 * (window.above + window.below) +
        4 * width.size + 1 := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) +
      ((window.above + window.below) +
        ((width.size + width.size) + ((width.size + width.size) + (1 + 0))))) = _
  omega

/-- Both retained phase flags agree with the original full-frame grouping. -/
lemma phases_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.2.2.2.1 =
      (grouping window state).2.2.2.2.2.1 := by
  apply Prod.ext
  · have same : wireEquiv window (firstPhaseBit window).wire =
        (SharedEEA.phase1Bit width).wire := by
      apply Fin.ext
      change physicalIndex window (firstPhaseBit window).wire.val =
        (SharedEEA.phase1Bit width).wire.val
      rw [firstPhaseBit_wire, SharedEEA.phase1Bit_wire]
      have complete := window.complete
      unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
      split_ifs <;> omega
    have actual := EncodedBit.FullPlacement.ofWires_read
      (groupedEncoding window) (encoding width)
      (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
      (firstPhaseBit window) (SharedEEA.phase1Bit width) same state
    change ((placement window).grouping state).2.2.2.2.2.1.1 =
      (SharedEEA.phase1Bit width).get state at actual
    rw [SharedEEA.phase1Bit_get] at actual
    exact actual
  · have same : wireEquiv window (secondPhaseBit window).wire =
        (SharedEEA.phase2Bit width).wire := by
      apply Fin.ext
      change physicalIndex window (secondPhaseBit window).wire.val =
        (SharedEEA.phase2Bit width).wire.val
      rw [secondPhaseBit_wire, SharedEEA.phase2Bit_wire]
      have complete := window.complete
      unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
      split_ifs <;> omega
    have actual := EncodedBit.FullPlacement.ofWires_read
      (groupedEncoding window) (encoding width)
      (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
      (secondPhaseBit window) (SharedEEA.phase2Bit width) same state
    change ((placement window).grouping state).2.2.2.2.2.1.2 =
      (SharedEEA.phase2Bit width).get state at actual
    rw [SharedEEA.phase2Bit_get] at actual
    exact actual

private lemma wordEquiv_above_bit {width : Nat} (window : Window width)
    (word : BitVec (width + 3)) (index : Fin window.above) :
    (wordEquiv window word).1.getMsbD index.val = word.getMsbD index.val := by
  rw [wordEquiv_above, BitVec.getMsbD_extractLsb']
  have complete := window.complete
  have within := index.isLt
  have bound : window.length + window.below + window.above - index.val ≤ width + 3 := by
    omega
  have position : width + 3 -
      (window.length + window.below + window.above - index.val) = index.val := by
    omega
  simp only [within, bound, decide_true, Bool.true_and, position]

private lemma wordEquiv_below_bit {width : Nat} (window : Window width)
    (word : BitVec (width + 3)) (index : Fin window.below) :
    (wordEquiv window word).2.2.getMsbD index.val =
      word.getMsbD (window.above + window.length + index.val) := by
  rw [wordEquiv_below, BitVec.getMsbD_extractLsb']
  have complete := window.complete
  have within := index.isLt
  have bound : window.below - index.val ≤ width + 3 := by omega
  have position : width + 3 - (window.below - index.val) =
      window.above + window.length + index.val := by omega
  simp only [Nat.zero_add, within, bound, decide_true, Bool.true_and, position]

private def firstPrefixBit {width : Nat} (window : Window width)
    (index : Fin window.above) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodLeftBit _ _
      (BinaryLabelEncoding.prodLeftBit _ _ (wordBit index)))

private lemma firstPrefixBit_wire {width : Nat} (window : Window width)
    (index : Fin window.above) :
    (firstPrefixBit window index).wire.val = 2 * window.length + 1 + index.val := by
  change (window.length + window.length + 1) + index.val = _
  omega

/-- The retained Work1 prefix reads the same original physical bits. -/
lemma firstPrefix_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.1.1 = (grouping window state).2.1.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin window.above := ⟨index, within⟩
  let physical : Fin (width + 3) := ⟨index, by
    have complete := window.complete
    omega⟩
  have same : wireEquiv window (firstPrefixBit window selected).wire =
      (firstWordBit width physical).wire := by
    apply Fin.ext
    change physicalIndex window (firstPrefixBit window selected).wire.val =
      (firstWordBit width physical).wire.val
    rw [firstPrefixBit_wire, firstWordBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (firstPrefixBit window selected) (firstWordBit width physical) same state
  change (wordBit selected).get ((placement window).grouping state).2.1.1 =
    (firstWordBit width physical).get state at actual
  rw [wordBit_get, firstWordBit_get] at actual
  have expected := wordEquiv_above_bit window state.firstWord selected
  change (grouping window state).2.1.1.getMsbD index =
    state.firstWord.getMsbD index at expected
  exact actual.trans expected.symm

private def secondPrefixBit {width : Nat} (window : Window width)
    (index : Fin window.above) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodLeftBit _ _
        (BinaryLabelEncoding.prodLeftBit _ _ (wordBit index))))

private lemma secondPrefixBit_wire {width : Nat} (window : Window width)
    (index : Fin window.above) :
    (secondPrefixBit window index).wire.val =
      2 * window.length + 1 + window.above + window.below + index.val := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) + index.val) = _
  omega

/-- The retained Work2 prefix reads the same original physical bits. -/
lemma secondPrefix_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.1.1 =
      (grouping window state).2.2.1.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin window.above := ⟨index, within⟩
  let physical : Fin (width + 3) := ⟨index, by
    have complete := window.complete
    omega⟩
  have same : wireEquiv window (secondPrefixBit window selected).wire =
      (secondWordBit width physical).wire := by
    apply Fin.ext
    change physicalIndex window (secondPrefixBit window selected).wire.val =
      (secondWordBit width physical).wire.val
    rw [secondPrefixBit_wire, secondWordBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (secondPrefixBit window selected) (secondWordBit width physical) same state
  change (wordBit selected).get ((placement window).grouping state).2.2.1.1 =
    (secondWordBit width physical).get state at actual
  rw [wordBit_get, secondWordBit_get] at actual
  have expected := wordEquiv_above_bit window state.secondWord selected
  change (grouping window state).2.2.1.1.getMsbD index =
    state.secondWord.getMsbD index at expected
  exact actual.trans expected.symm

private def firstSuffixBit {width : Nat} (window : Window width)
    (index : Fin window.below) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodLeftBit _ _
      (BinaryLabelEncoding.prodRightBit _ _ (wordBit index)))

private lemma firstSuffixBit_wire {width : Nat} (window : Window width)
    (index : Fin window.below) :
    (firstSuffixBit window index).wire.val =
      2 * window.length + 1 + window.above + index.val := by
  change (window.length + window.length + 1) + (window.above + index.val) = _
  omega

/-- The retained Work1 suffix reads the same original physical bits. -/
lemma firstSuffix_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.1.2 = (grouping window state).2.1.2 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin window.below := ⟨index, within⟩
  let physical : Fin (width + 3) := ⟨window.above + window.length + index, by
    have complete := window.complete
    omega⟩
  have same : wireEquiv window (firstSuffixBit window selected).wire =
      (firstWordBit width physical).wire := by
    apply Fin.ext
    change physicalIndex window (firstSuffixBit window selected).wire.val =
      (firstWordBit width physical).wire.val
    rw [firstSuffixBit_wire, firstWordBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    change physicalIndex window
      (2 * window.length + 1 + window.above + index) =
        window.above + window.length + index
    rw [physicalIndex, if_neg (by omega)]
    unfold complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (firstSuffixBit window selected) (firstWordBit width physical) same state
  change (wordBit selected).get ((placement window).grouping state).2.1.2 =
    (firstWordBit width physical).get state at actual
  rw [wordBit_get, firstWordBit_get] at actual
  have expected := wordEquiv_below_bit window state.firstWord selected
  change (grouping window state).2.1.2.getMsbD index =
    state.firstWord.getMsbD (window.above + window.length + index) at expected
  exact actual.trans expected.symm

private def secondSuffixBit {width : Nat} (window : Window width)
    (index : Fin window.below) : EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodLeftBit _ _
        (BinaryLabelEncoding.prodRightBit _ _ (wordBit index))))

private lemma secondSuffixBit_wire {width : Nat} (window : Window width)
    (index : Fin window.below) :
    (secondSuffixBit window index).wire.val =
      2 * window.length + 1 + window.above + window.below +
        window.above + index.val := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) + (window.above + index.val)) = _
  omega

/-- The retained Work2 suffix reads the same original physical bits. -/
lemma secondSuffix_field {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2.2.1.2 =
      (grouping window state).2.2.1.2 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin window.below := ⟨index, within⟩
  let physical : Fin (width + 3) := ⟨window.above + window.length + index, by
    have complete := window.complete
    omega⟩
  have same : wireEquiv window (secondSuffixBit window selected).wire =
      (secondWordBit width physical).wire := by
    apply Fin.ext
    change physicalIndex window (secondSuffixBit window selected).wire.val =
      (secondWordBit width physical).wire.val
    rw [secondSuffixBit_wire, secondWordBit_wire]
    have complete := window.complete
    have bound := selected.isLt
    change physicalIndex window
      (2 * window.length + 1 + window.above + window.below +
        window.above + index) =
        width + 3 + (window.above + window.length + index)
    rw [physicalIndex, if_neg (by omega)]
    unfold complementPhysicalIndex
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width) (wireEquiv window)
    (secondSuffixBit window selected) (secondWordBit width physical) same state
  change (wordBit selected).get ((placement window).grouping state).2.2.1.2 =
    (secondWordBit width physical).get state at actual
  rw [wordBit_get, secondWordBit_get] at actual
  have expected := wordEquiv_below_bit window state.secondWord selected
  change (grouping window state).2.2.1.2.getMsbD index =
    state.secondWord.getMsbD (window.above + window.length + index) at expected
  exact actual.trans expected.symm

/-- The strict wire placement reconstructs every field of the original source grouping. -/
lemma placement_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    (placement window).grouping state = grouping window state := by
  apply Prod.ext
  · exact focus_grouping window state
  · apply Prod.ext
    · apply Prod.ext
      · exact firstPrefix_field window state
      · exact firstSuffix_field window state
    · apply Prod.ext
      · apply Prod.ext
        · exact secondPrefix_field window state
        · exact secondSuffix_field window state
      · apply Prod.ext
        · apply Prod.ext
          · exact coefficient_field window state
          · exact quotient_field window state
        · apply Prod.ext
          · apply Prod.ext
            · exact divisor_field window state
            · exact shift_field window state
          · apply Prod.ext
            · exact phases_grouping window state
            · apply Prod.ext
              · have actual := work_grouping window state
                change ((placement window).grouping state).2.2.2.2.2.2.1 =
                  (grouping window state).2.2.2.2.2.2.1 at actual
                exact actual
              · have actual := control_grouping window state
                change ((placement window).grouping state).2.2.2.2.2.2.2 =
                  (grouping window state).2.2.2.2.2.2.2 at actual
                exact actual

/-- All source and target semantic fields use the original grouping equivalence. -/
lemma placement_grouping_equiv {width : Nat} (window : Window width) :
    (placement window).grouping = grouping window :=
  Equiv.ext (placement_grouping window)

/-- A second physical placement that fixes the complementary wire interval retains every field. -/
lemma complement_ofWires_fixed {width : Nat} (window : Window width)
    (otherWires : Fin (groupedEncoding window).width ≃ Fin (encoding width).width)
    (fixed : ∀ index : Fin (groupedEncoding window).width,
      2 * window.length + 1 ≤ index.val → otherWires index = wireEquiv window index)
    (state : Registers width) :
    ((EncodedBit.FullPlacement.ofWires (groupedEncoding window) (encoding width)
      (groupedEncoding_surjective window) (encoding_surjective width)
      otherWires).grouping state).2 = (grouping window state).2 := by
  let source := groupedEncoding window
  let target := encoding width
  let ordinary := placement window
  let other := EncodedBit.FullPlacement.ofWires source target
    (groupedEncoding_surjective window) (encoding_surjective width) otherWires
  have compare (index : Fin source.width) (same : otherWires index = wireEquiv window index) :
      (source.encode (other.grouping state)).val.testBit index.rev.val =
        (source.encode (ordinary.grouping state)).val.testBit index.rev.val := by
    have a := EncodedBit.FullPlacement.wireBasis_bit source target otherWires
      (source.encode (other.grouping state)) index
    have b := EncodedBit.FullPlacement.wireBasis_bit source target (wireEquiv window)
      (source.encode (ordinary.grouping state)) index
    change (other.basis (source.encode (other.grouping state))).val.testBit
      (otherWires index).rev.val = _ at a
    change (ordinary.basis (source.encode (ordinary.grouping state))).val.testBit
      ((wireEquiv window) index).rev.val = _ at b
    rw [other.basis_encode state, same] at a
    rw [ordinary.basis_encode state] at b
    exact a.symm.trans b
  have encoded : (complementEncoding window).encode (other.grouping state).2 =
      (complementEncoding window).encode (ordinary.grouping state).2 := by
    apply (BinaryBasis.bigEndianEquiv (complementEncoding window).width).symm.injective
    funext index
    apply finTwoEquiv.injective
    simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
    let full : Fin source.width := BinaryLabelEncoding.prodRightWire
      (Addition.TTK.overflowEncoding window.length) (complementEncoding window) index
    have bound : 2 * window.length + 1 ≤ full.val := by
      rw [BinaryLabelEncoding.prodRightWire_val]
      change 2 * window.length + 1 ≤ (window.length + window.length + 1) + index.val
      omega
    have position : full.rev.val = index.rev.val := by
      rw [Fin.val_rev, Fin.val_rev]
      change ((window.length + window.length + 1) +
        (complementEncoding window).width) -
          (((window.length + window.length + 1) + index.val) + 1) =
            (complementEncoding window).width - (index.val + 1)
      have within := index.isLt
      omega
    have rightBit (pair : Addition.TTK.OverflowRegisters window.length × Complement window) :
        (source.encode pair).val.testBit full.rev.val =
          ((complementEncoding window).encode pair.2).val.testBit index.rev.val := by
      rw [position]
      change (prodEquiv
        ((Addition.TTK.overflowEncoding window.length).encode pair.1,
          (complementEncoding window).encode pair.2)).val.testBit index.rev.val = _
      exact prodEquiv_testBit_right _ _ index.rev
    rw [← rightBit (other.grouping state), ← rightBit (ordinary.grouping state)]
    exact compare full (fixed full bound)
  apply (complementEncoding window).encode_injective
  rw [← placement_grouping window state]
  exact encoded

/-- Reassemble and physically place the existing body, retaining the full original live frame. -/
def place {width : Nat} (window : Window width)
    {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QubitLayout.canonical (groupedEncoding window).width).toQuantum) :
    UnitaryCircuit gates oracles (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement window).place body

/-- Transport the complete grouped action through the physically induced field grouping. -/
def placedStep {width : Nat} (window : Window width)
    (action : Addition.TTK.OverflowRegisters window.length × Complement window →
      Addition.TTK.OverflowRegisters window.length × Complement window)
    (state : Registers width) : Registers width :=
  (placement window).step action state

/-- Strict physical placement has the registered full-frame arithmetic semantics. -/
lemma placedStep_eq {width : Nat} (window : Window width)
    (action : Addition.TTK.OverflowRegisters window.length × Complement window →
      Addition.TTK.OverflowRegisters window.length × Complement window)
    (state : Registers width) :
    placedStep window action state =
      (grouping window).symm (action (grouping window state)) := by
  unfold placedStep EncodedBit.FullPlacement.step
  rw [placement_grouping_equiv]

/-- Exact basis amplitudes of the actual body survive the original-coordinate placement. -/
lemma place_realizes {width : Nat} (window : Window width)
    {gates : GateModel} {oracles : OracleModel}
    {environment : oracles.Interpretation}
    {body : UnitaryCircuit gates oracles
      (QubitLayout.canonical (groupedEncoding window).width).toQuantum}
    {action : Addition.TTK.OverflowRegisters window.length × Complement window →
      Addition.TTK.OverflowRegisters window.length × Complement window}
    (realizes : UnitaryCircuit.Realizes (groupedEncoding window) body environment action) :
    UnitaryCircuit.Realizes (encoding width) (place window body) environment
      (placedStep window action) :=
  (placement window).place_realizes realizes

/-- Every actual native event remains present and ordered after physical placement. -/
lemma place_eventTrace {width : Nat} (window : Window width)
    {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QubitLayout.canonical (groupedEncoding window).width).toQuantum) :
    (place window body).eventTrace = body.eventTrace :=
  (placement window).place_eventTrace body

/-- Placement preserves the actual body's depth for every native duration assignment. -/
lemma place_evaluatedEventDepth {width : Nat} (window : Window width)
    {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QubitLayout.canonical (groupedEncoding window).width).toQuantum)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (place window body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration :=
  (placement window).place_evaluatedEventDepth body duration

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowPlacement
