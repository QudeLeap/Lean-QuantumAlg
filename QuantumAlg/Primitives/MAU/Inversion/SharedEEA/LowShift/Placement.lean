/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Registers
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

/-!
# Place an actual low-counter program on the original shared registers

The complete Work1 word, low shift, and Phase2 form the native arithmetic
interface. Every other named source field is tensored alongside it
[LYL+26, sec_EEA/sub_regshare.tex:16-26]. The exact basis map decodes and
reassembles those same named fields through their actual binary encodings.
Its inverse is the same proved field grouping, rather than an equivalence
chosen from cardinalities.

The physical map is applied to the existing native leaves and uses exactly
the addresses checked by the corresponding semantic bit lenses. The
original ordered events remain intact. This is placement of an existing
program, not an implementation of an arbitrary semantic permutation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LowShiftPlacement

noncomputable section

open LowShiftRegisters

def remainderEncoding (width : Nat) : BinaryLabelEncoding (Remainder width) :=
  BinaryLabelEncoding.prod (wordEncoding (width + 3))
    (BinaryLabelEncoding.prod (lengthPairEncoding width)
      (BinaryLabelEncoding.prod (wordEncoding width.size) flagEncoding))

private theorem remainder_surjective (width : Nat) :
    Function.Surjective (remainderEncoding width).encode :=
  prod_surjective _ _ (word_surjective _) (prod_surjective _ _
    (prod_surjective _ _ (word_surjective _) (word_surjective _))
    (prod_surjective _ _ (word_surjective _)
      (prod_surjective _ _ (prod_surjective _ _ bool_surjective bool_surjective)
        (prod_surjective _ _ bool_surjective bool_surjective))))

private theorem focus_surjective (width : Nat) :
    Function.Surjective (Addition.HRS.bridgeEncoding (width + 3) width.size).encode := by
  have raw : Function.Surjective
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width.size)
          (BinaryLabelEncoding.finIdentity (width + 3))) BinaryLabelEncoding.bool).encode :=
    prod_surjective _ _
      (prod_surjective _ _ Function.surjective_id Function.surjective_id)
      bool_surjective
  intro label
  obtain ⟨value, same⟩ := raw label
  refine ⟨(Addition.HRS.bridgeGrouping (width + 3) width.size).symm value, ?_⟩
  change (BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width.size)
      (BinaryLabelEncoding.finIdentity (width + 3))) BinaryLabelEncoding.bool).encode
        (Addition.HRS.bridgeGrouping (width + 3) width.size
          ((Addition.HRS.bridgeGrouping (width + 3) width.size).symm value)) = label
  rw [Equiv.apply_symm_apply]
  exact same

@[implicit_reducible]
def groupedEncoding (width : Nat) : BinaryLabelEncoding
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size × Remainder width) :=
  BinaryLabelEncoding.prod (Addition.HRS.bridgeEncoding (width + 3) width.size)
    (remainderEncoding width)

private def groupedLabelEquiv (width : Nat) :
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size × Remainder width) ≃
      (Qubits (groupedEncoding width).width).Index :=
  Equiv.ofBijective (groupedEncoding width).encode
    ⟨(groupedEncoding width).encode_injective,
      prod_surjective _ _ (focus_surjective width) (remainder_surjective width)⟩

private def registerLabelEquiv (width : Nat) :
    Registers width ≃ (Qubits (encoding width).width).Index :=
  Equiv.ofBijective (encoding width).encode
    ⟨(encoding width).encode_injective, encoding_surjective width⟩

/-- Decode the actual product fields and reassemble the same full source register label. -/
def indexEquiv (width : Nat) :
    (Qubits (groupedEncoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  (groupedLabelEquiv width).symm.trans
    ((grouping width).symm.trans (registerLabelEquiv width))

/-- The complete explicit grouping is exactly the basis transport, for every field value. -/
theorem indexEquiv_encode (width : Nat) (state : Registers width) :
    indexEquiv width ((groupedEncoding width).encode (grouping width state)) =
      (encoding width).encode state := by
  change registerLabelEquiv width ((grouping width).symm
    ((groupedLabelEquiv width).symm (groupedLabelEquiv width (grouping width state)))) =
      registerLabelEquiv width state
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Complete grouped carrier width: HRS shift, borrowed Work1, Phase2, then all spectators. -/
theorem grouped_width (width : Nat) :
    (groupedEncoding width).width =
      (width.size + (width + 3) + 1) + ((width + 3) + 3 * width.size + 4) := by
  change (width.size + (width + 3) + 1) +
    ((width + 3) + ((width.size + width.size) + (width.size + ((1 + 1) + (1 + 1))))) = _
  omega

/-- Actual original positions of the retained Work2, lengths, and four flags. -/
def complementPhysicalIndex (width index : Nat) : Nat :=
  if index < width + 3 then width + 3 + index
  else if index < width + 3 + 3 * width.size then
    2 * (width + 3) + (index - (width + 3))
  else if index = width + 3 + 3 * width.size then
    2 * (width + 3) + 4 * width.size
  else 2 * (width + 3) + 4 * width.size + 1 +
    (index - (width + 3 + 3 * width.size))

/-- Every grouped slot maps to precisely its original physical wire. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < width.size + (width + 3) + 1 then
    LowShiftRegisters.physicalIndex width index
  else complementPhysicalIndex width (index - (width.size + (width + 3) + 1))

private theorem focus_injective (width : Nat) :
    Function.Injective (fun index : Fin (width.size + (width + 3) + 1) =>
      LowShiftRegisters.physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  change LowShiftRegisters.physicalIndex width left.val =
    LowShiftRegisters.physicalIndex width right.val at same
  unfold LowShiftRegisters.physicalIndex at same
  split_ifs at same <;> omega

private theorem complement_injective (width : Nat) :
    Function.Injective (fun index : Fin ((width + 3) + 3 * width.size + 4) =>
      complementPhysicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  change complementPhysicalIndex width left.val = complementPhysicalIndex width right.val at same
  unfold complementPhysicalIndex at same
  split_ifs at same <;> omega

private theorem focus_ne_complement (width : Nat)
    (focus : Fin (width.size + (width + 3) + 1))
    (rest : Fin ((width + 3) + 3 * width.size + 4)) :
    LowShiftRegisters.physicalIndex width focus.val ≠
      complementPhysicalIndex width rest.val := by
  intro same
  have focusBound := focus.isLt
  have restBound := rest.isLt
  unfold LowShiftRegisters.physicalIndex complementPhysicalIndex at same
  split_ifs at same <;> omega

/-- The full map never aliases an HRS or spectator wire. -/
theorem physicalIndex_injective (width : Nat) :
    Function.Injective
      (fun index : Fin (groupedEncoding width).width => physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  have total := grouped_width width
  change physicalIndex width left.val = physicalIndex width right.val at same
  unfold physicalIndex at same
  by_cases leftFocus : left.val < width.size + (width + 3) + 1
  · rw [if_pos leftFocus] at same
    by_cases rightFocus : right.val < width.size + (width + 3) + 1
    · rw [if_pos rightFocus] at same
      exact congrArg (fun index : Fin (width.size + (width + 3) + 1) => index.val)
        (focus_injective width (a₁ := ⟨left.val, leftFocus⟩)
          (a₂ := ⟨right.val, rightFocus⟩) same)
    · rw [if_neg rightFocus] at same
      exact False.elim (focus_ne_complement width ⟨left.val, leftFocus⟩
        ⟨right.val - (width.size + (width + 3) + 1), by omega⟩ same)
  · rw [if_neg leftFocus] at same
    by_cases rightFocus : right.val < width.size + (width + 3) + 1
    · rw [if_pos rightFocus] at same
      exact False.elim (focus_ne_complement width ⟨right.val, rightFocus⟩
        ⟨left.val - (width.size + (width + 3) + 1), by omega⟩ same.symm)
    · rw [if_neg rightFocus] at same
      have values := congrArg
        (fun index : Fin ((width + 3) + 3 * width.size + 4) => index.val)
        (complement_injective width
          (a₁ := ⟨left.val - (width.size + (width + 3) + 1), by omega⟩)
          (a₂ := ⟨right.val - (width.size + (width + 3) + 1), by omega⟩) same)
      change left.val - (width.size + (width + 3) + 1) =
        right.val - (width.size + (width + 3) + 1) at values
      omega

/-- Every mapped bit stays within the complete original frame. -/
theorem physicalIndex_within (width : Nat) (index : Fin (groupedEncoding width).width) :
    physicalIndex width index.val < (encoding width).width := by
  rw [encoding_width]
  have bound : index.val <
      (width.size + (width + 3) + 1) + ((width + 3) + 3 * width.size + 4) :=
    index.isLt.trans_le (grouped_width width).le
  unfold physicalIndex LowShiftRegisters.physicalIndex complementPhysicalIndex
  split_ifs <;> omega

/-- Complete grouped-to-source wire map. -/
def wireMap (width : Nat) :
    Fin (groupedEncoding width).width → Fin (encoding width).width :=
  fun index => ⟨physicalIndex width index.val, physicalIndex_within width index⟩

theorem wireMap_injective (width : Nat) : Function.Injective (wireMap width) := by
  intro left right same
  exact physicalIndex_injective width (congrArg Fin.val same)

/-- Equal-width injectivity covers every original source coordinate. -/
theorem wireMap_surjective (width : Nat) : Function.Surjective (wireMap width) := by
  have sameWidth : (groupedEncoding width).width = (encoding width).width := by
    rw [grouped_width, encoding_width]
    omega
  let endomap := fun index : Fin (groupedEncoding width).width =>
    Fin.cast sameWidth.symm (wireMap width index)
  have injective : Function.Injective endomap := by
    intro left right same
    apply wireMap_injective width
    exact Fin.cast_injective sameWidth.symm same
  intro target
  obtain ⟨source, same⟩ :=
    Finite.surjective_of_injective injective (Fin.cast sameWidth.symm target)
  exact ⟨source, Fin.cast_injective sameWidth.symm same⟩

/-- The HRS interface and its complete complement permute the original wire frame. -/
def wireEquiv (width : Nat) :
    Fin (groupedEncoding width).width ≃ Fin (encoding width).width :=
  Equiv.ofBijective (wireMap width)
    ⟨wireMap_injective width, wireMap_surjective width⟩

/-- Native HRS addresses are retained as physical source addresses. -/
theorem physicalIndex_focus (width : Nat)
    (index : Fin (width.size + (width + 3) + 1)) :
    physicalIndex width index.val = LowShiftRegisters.physicalIndex width index.val :=
  if_pos index.isLt

/-- The semantic basis and physical map are both derived from the same complete wires. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (groupedEncoding width) (encoding width) :=
  EncodedBit.FullPlacement.ofWires (groupedEncoding width) (encoding width)
    (prod_surjective _ _ (focus_surjective width) (remainder_surjective width))
    (encoding_surjective width) (wireEquiv width)

private theorem placed_read (width : Nat) (state : Registers width)
    (source : EncodedBit (groupedEncoding width))
    (target : EncodedBit (encoding width))
    (same : wireEquiv width source.wire = target.wire) :
    source.get ((placement width).grouping state) = target.get state :=
  EncodedBit.FullPlacement.ofWires_read (groupedEncoding width) (encoding width)
    (prod_surjective _ _ (focus_surjective width) (remainder_surjective width))
    (encoding_surjective width) (wireEquiv width) source target same state

/-- One native high-word bit in the physical shift prefix. -/
private def shiftFocusBit (width : Nat) (index : Fin width.size) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodLeftBit _ _
    (Addition.HRS.bridgeHighBit (width + 3) width.size index.rev)

private theorem shiftFocusBit_wire (width : Nat) (index : Fin width.size) :
    (shiftFocusBit width index).wire.val = index.val := by
  change (Addition.HRS.bridgeHighBit (width + 3) width.size index.rev).wire.val = _
  rw [Addition.HRS.hrsBridgeHighBit_wire, Fin.val_rev]
  have bound := index.isLt
  omega

/-- The target bit is read at its original shift address. -/
theorem placement_shift_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (Addition.HRS.bridgeHighBit (width + 3) width.size index.rev).get
      ((placement width).grouping state).1 =
      (shiftBit width index).get state := by
  have same : wireEquiv width (shiftFocusBit width index).wire =
      (shiftBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (shiftFocusBit width index).wire.val =
      (shiftBit width index).wire.val
    rw [shiftFocusBit_wire]
    have inside : index.val < width.size + (width + 3) + 1 := by
      have bound := index.isLt
      omega
    rw [physicalIndex, if_pos inside]
    exact LowShiftRegisters.physicalIndex_shift width index
  exact placed_read width state (shiftFocusBit width index) (shiftBit width index) same

/-- One native low-word bit in the physical borrowed Work1 segment. -/
private def workFocusBit (width : Nat) (index : Fin (width + 3)) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodLeftBit _ _
    (Addition.HRS.bridgeLowBit (width + 3) width.size index.rev)

private theorem workFocusBit_wire (width : Nat) (index : Fin (width + 3)) :
    (workFocusBit width index).wire.val = width.size + index.val := by
  change (Addition.HRS.bridgeLowBit (width + 3) width.size index.rev).wire.val = _
  rw [Addition.HRS.hrsBridgeLowBit_wire, Fin.val_rev]
  have bound := index.isLt
  omega

/-- The borrowed bit is read at its original Work1 address. -/
theorem placement_work_bit (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    (Addition.HRS.bridgeLowBit (width + 3) width.size index.rev).get
      ((placement width).grouping state).1 =
      (firstWordBit width index).get state := by
  have same : wireEquiv width (workFocusBit width index).wire =
      (firstWordBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (workFocusBit width index).wire.val =
      (firstWordBit width index).wire.val
    rw [workFocusBit_wire]
    have inside : width.size + index.val < width.size + (width + 3) + 1 := by
      have bound := index.isLt
      omega
    rw [physicalIndex, if_pos inside]
    exact LowShiftRegisters.physicalIndex_work width index
  exact placed_read width state (workFocusBit width index) (firstWordBit width index) same

/-- The control of the HRS bridge reads exactly the original Phase2 bit. -/
private def phaseFocusBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodLeftBit _ _
    (Addition.HRS.bridgeDirtyBit (width + 3) width.size)

theorem placement_phase2 (width : Nat) (state : Registers width) :
    ((placement width).grouping state).1.2 = state.flags.second := by
  have same : wireEquiv width (phaseFocusBit width).wire = (phase2Bit width).wire := by
    apply Fin.ext
    change physicalIndex width (phaseFocusBit width).wire.val = (phase2Bit width).wire.val
    change physicalIndex width (width.size + (width + 3)) = _
    have inside : width.size + (width + 3) < width.size + (width + 3) + 1 := by omega
    rw [physicalIndex, if_pos inside]
    exact LowShiftRegisters.physicalIndex_control width
  have actual := placed_read width state (phaseFocusBit width) (phase2Bit width) same
  change ((placement width).grouping state).1.2 = (phase2Bit width).get state at actual
  simpa only [phase2Bit_get] using actual

/-- Every physical borrowed Work1 bit agrees with the registered source grouping. -/
theorem placement_grouping_work (width : Nat) (state : Registers width) :
    ((placement width).grouping state).1.1.1 = (grouping width state).1.1.1 := by
  apply (BinaryBasis.bigEndianEquiv (width + 3)).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  have actual := placement_work_bit width index state
  have expected := LowShiftRegisters.grouping_work_bit width index.rev state
  rw [Fin.rev_rev] at expected
  rw [Addition.HRS.hrsBridgeLowBit_get] at actual expected
  exact actual.trans expected.symm

/-- Every physical low-shift target bit agrees with the registered source grouping. -/
theorem placement_grouping_shift (width : Nat) (state : Registers width) :
    ((placement width).grouping state).1.1.2 = (grouping width state).1.1.2 := by
  apply (BinaryBasis.bigEndianEquiv width.size).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  have actual := placement_shift_bit width index state
  have expected := LowShiftRegisters.grouping_shift_bit width index.rev state
  rw [Fin.rev_rev] at expected
  rw [Addition.HRS.hrsBridgeHighBit_get] at actual expected
  exact actual.trans expected.symm

/-- One retained Work2 bit in the complete complementary product. -/
private def work2Bit (width : Nat) (index : Fin (width + 3)) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodLeftBit _ _ (wordBit index))

private theorem work2Bit_wire (width : Nat) (index : Fin (width + 3)) :
    (work2Bit width index).wire.val =
      width.size + (width + 3) + 1 + index.val := by
  rfl

theorem placement_work2_bit (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    (wordBit index).get ((placement width).grouping state).2.1 =
      (secondWordBit width index).get state := by
  have same : wireEquiv width (work2Bit width index).wire =
      (secondWordBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (work2Bit width index).wire.val =
      (secondWordBit width index).wire.val
    rw [work2Bit_wire, secondWordBit_wire]
    have outside : ¬width.size + (width + 3) + 1 + index.val <
        width.size + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    rw [complementPhysicalIndex, if_pos index.isLt]
  exact placed_read width state (work2Bit width index) (secondWordBit width index) same

/-- The complete wire-derived grouping retains exactly Work2. -/
theorem placement_grouping_work2 (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.1 = (grouping width state).2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin (width + 3) := ⟨index, within⟩
  have actual := placement_work2_bit width selected state
  rw [wordBit_get, secondWordBit_get] at actual
  exact actual

private def lengthPairBit (width : Nat)
    (bit : EncodedBit (lengthPairEncoding width)) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodLeftBit _ _ bit))

private def coefficientBit (width : Nat) (index : Fin width.size) :
    EncodedBit (groupedEncoding width) :=
  lengthPairBit width
    (BinaryLabelEncoding.prodLeftBit (wordEncoding width.size) (wordEncoding width.size)
      (wordBit index))

private theorem coefficientBit_wire (width : Nat) (index : Fin width.size) :
    (coefficientBit width index).wire.val =
      width.size + (width + 3) + 1 + (width + 3 + index.val) := by
  rfl

theorem placement_coefficient_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (wordBit index).get ((placement width).grouping state).2.2.1.1 =
      (coefficientLengthBit width index).get state := by
  have same : wireEquiv width (coefficientBit width index).wire =
      (coefficientLengthBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (coefficientBit width index).wire.val =
      (coefficientLengthBit width index).wire.val
    rw [coefficientBit_wire, coefficientLengthBit_wire]
    have outside : ¬width.size + (width + 3) + 1 + (width + 3 + index.val) <
        width.size + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    unfold complementPhysicalIndex
    have bound := index.isLt
    split_ifs <;> omega
  exact placed_read width state (coefficientBit width index)
    (coefficientLengthBit width index) same

private def quotientBit (width : Nat) (index : Fin width.size) :
    EncodedBit (groupedEncoding width) :=
  lengthPairBit width
    (BinaryLabelEncoding.prodRightBit (wordEncoding width.size) (wordEncoding width.size)
      (wordBit index))

private theorem quotientBit_wire (width : Nat) (index : Fin width.size) :
    (quotientBit width index).wire.val =
      width.size + (width + 3) + 1 + (width + 3 + width.size + index.val) := by
  change (width.size + (width + 3) + 1) +
    ((width + 3) + (width.size + index.val)) = _
  omega

theorem placement_quotient_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (wordBit index).get ((placement width).grouping state).2.2.1.2 =
      (quotientLengthBit width index).get state := by
  have same : wireEquiv width (quotientBit width index).wire =
      (quotientLengthBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (quotientBit width index).wire.val =
      (quotientLengthBit width index).wire.val
    rw [quotientBit_wire, quotientLengthBit_wire]
    have outside : ¬width.size + (width + 3) + 1 +
        (width + 3 + width.size + index.val) < width.size + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    unfold complementPhysicalIndex
    have bound := index.isLt
    split_ifs <;> omega
  exact placed_read width state (quotientBit width index)
    (quotientLengthBit width index) same

private def divisorBit (width : Nat) (index : Fin width.size) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodLeftBit (wordEncoding width.size) flagEncoding
          (wordBit index))))

private theorem divisorBit_wire (width : Nat) (index : Fin width.size) :
    (divisorBit width index).wire.val =
      width.size + (width + 3) + 1 + (width + 3 + 2 * width.size + index.val) := by
  change (width.size + (width + 3) + 1) +
    ((width + 3) + ((width.size + width.size) + index.val)) = _
  omega

theorem placement_divisor_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (wordBit index).get ((placement width).grouping state).2.2.2.1 =
      (divisorLengthBit width index).get state := by
  have same : wireEquiv width (divisorBit width index).wire =
      (divisorLengthBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (divisorBit width index).wire.val =
      (divisorLengthBit width index).wire.val
    rw [divisorBit_wire, divisorLengthBit_wire]
    have outside : ¬width.size + (width + 3) + 1 +
        (width + 3 + 2 * width.size + index.val) < width.size + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    unfold complementPhysicalIndex
    have bound := index.isLt
    split_ifs <;> omega
  exact placed_read width state (divisorBit width index)
    (divisorLengthBit width index) same

theorem placement_grouping_lengths (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.1 = (grouping width state).2.2.1 ∧
      ((placement width).grouping state).2.2.2.1 = (grouping width state).2.2.2.1 := by
  constructor
  · apply Prod.ext
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      let selected : Fin width.size := ⟨index, within⟩
      have actual := placement_coefficient_bit width selected state
      rw [wordBit_get, coefficientLengthBit_get] at actual
      exact actual
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      let selected : Fin width.size := ⟨index, within⟩
      have actual := placement_quotient_bit width selected state
      rw [wordBit_get, quotientLengthBit_get] at actual
      exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := placement_divisor_bit width selected state
    rw [wordBit_get, divisorLengthBit_get] at actual
    exact actual

/-- Lift each of the four retained flags through the complete complement. -/
private def retainedFlagBit (width : Nat) (bit : EncodedBit flagEncoding) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodRightBit (wordEncoding width.size) flagEncoding bit)))

private theorem retainedFlagBit_wire (width : Nat) (bit : EncodedBit flagEncoding) :
    (retainedFlagBit width bit).wire.val = width.size + (width + 3) + 1 +
      ((width + 3) + 3 * width.size + bit.wire.val) := by
  change (width.size + (width + 3) + 1) +
    ((width + 3) + ((width.size + width.size) +
      (width.size + bit.wire.val))) = _
  omega

private theorem retainedFlagBit_physical (width : Nat) (bit : EncodedBit flagEncoding) :
    physicalIndex width (retainedFlagBit width bit).wire.val =
      if bit.wire.val = 0 then 2 * (width + 3) + 4 * width.size
      else 2 * (width + 3) + 4 * width.size + 1 + bit.wire.val := by
  rw [retainedFlagBit_wire]
  have outside : ¬width.size + (width + 3) + 1 +
      ((width + 3) + 3 * width.size + bit.wire.val) <
      width.size + (width + 3) + 1 := by omega
  rw [physicalIndex, if_neg outside]
  simp only [Nat.add_sub_cancel_left]
  unfold complementPhysicalIndex
  have bound := bit.wire.isLt
  change bit.wire.val < 4 at bound
  split_ifs <;> omega

private def firstFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodLeftBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

theorem placement_phase1 (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.1.1 = state.flags.first := by
  have same : wireEquiv width (firstFlagBit width).wire = (phase1Bit width).wire := by
    apply Fin.ext
    change physicalIndex width (firstFlagBit width).wire.val = (phase1Bit width).wire.val
    unfold firstFlagBit
    rw [retainedFlagBit_physical, phase1Bit_wire]
    rfl
  have actual := placed_read width state (firstFlagBit width) (phase1Bit width) same
  change ((placement width).grouping state).2.2.2.2.1.1 =
    (phase1Bit width).get state at actual
  simpa only [phase1Bit_get] using actual

private def signFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodLeftBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

theorem placement_sign (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.1.2 = state.flags.sign := by
  have same : wireEquiv width (signFlagBit width).wire = (signBit width).wire := by
    apply Fin.ext
    change physicalIndex width (signFlagBit width).wire.val = (signBit width).wire.val
    unfold signFlagBit
    rw [retainedFlagBit_physical, signBit_wire]
    rfl
  have actual := placed_read width state (signFlagBit width) (signBit width) same
  change ((placement width).grouping state).2.2.2.2.1.2 =
    (signBit width).get state at actual
  simpa only [signBit_get] using actual

private def iterationFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodRightBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

theorem placement_iteration (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.2.1 = state.flags.iteration := by
  have same : wireEquiv width (iterationFlagBit width).wire =
      (iterationBit width).wire := by
    apply Fin.ext
    change physicalIndex width (iterationFlagBit width).wire.val =
      (iterationBit width).wire.val
    unfold iterationFlagBit
    rw [retainedFlagBit_physical, iterationBit_wire]
    rfl
  have actual := placed_read width state (iterationFlagBit width) (iterationBit width) same
  change ((placement width).grouping state).2.2.2.2.2.1 =
    (iterationBit width).get state at actual
  simpa only [iterationBit_get] using actual

private def controlFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodRightBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

theorem placement_control (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.2.2 = state.control := by
  have same : wireEquiv width (controlFlagBit width).wire = (controlBit width).wire := by
    apply Fin.ext
    change physicalIndex width (controlFlagBit width).wire.val = (controlBit width).wire.val
    unfold controlFlagBit
    rw [retainedFlagBit_physical, controlBit_wire]
    rfl
  have actual := placed_read width state (controlFlagBit width) (controlBit width) same
  change ((placement width).grouping state).2.2.2.2.2.2 =
    (controlBit width).get state at actual
  simpa only [controlBit_get] using actual

/-- The strict wire placement agrees with every registered source field. -/
theorem placement_grouping (width : Nat) (state : Registers width) :
    (placement width).grouping state = grouping width state := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · exact placement_grouping_work width state
      · exact placement_grouping_shift width state
    · exact placement_phase2 width state
  · apply Prod.ext
    · exact placement_grouping_work2 width state
    · apply Prod.ext
      · exact (placement_grouping_lengths width state).1
      · apply Prod.ext
        · exact (placement_grouping_lengths width state).2
        · apply Prod.ext
          · apply Prod.ext
            · exact placement_phase1 width state
            · exact placement_sign width state
          · apply Prod.ext
            · exact placement_iteration width state
            · exact placement_control width state

theorem placement_grouping_eq (width : Nat) :
    (placement width).grouping = grouping width := by
  apply Equiv.ext
  exact placement_grouping width

/-- Full-frame action of a native bridge step under the source grouping. -/
def placedStep {width : Nat}
    (action : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size →
      Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size)
    (state : Registers width) : Registers width :=
  (grouping width).symm (action (grouping width state).1, (grouping width state).2)

end

end QuantumAlg.MAU.Inversion.SharedEEA.LowShiftPlacement
