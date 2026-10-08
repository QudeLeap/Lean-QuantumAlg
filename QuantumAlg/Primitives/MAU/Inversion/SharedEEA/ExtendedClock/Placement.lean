/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Registers
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Unloading

/-!
# Complete basis and physical placement for the existing-wire extended clock

The actual HRS work, target, and control coordinates are extended by all
remaining original bits. The basis equivalence explicitly decodes this
complete product and reassembles the original full register frame. The
physical map matches Work2, the two Work1 padding positions, the old
shift field, Phase2, and every spectator
[HRS16, paper.tex:219-226;
LYL+26, sec_EEA/sub_regshare.tex:16-26].

Both maps are exact on arbitrary frames, including nonzero high bits and
arbitrary borrowed Work2. They allocate no workspace and emit no gates.
The generic placement owner will retain the literal trace of the actual
HRS body once that body is supplied.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockPlacement

noncomputable section

open ExtendedClockRegisters

/-- Original main/last Work1 bits followed by the three lengths and four remaining controls. -/
def remainderEncoding (width : Nat) : BinaryLabelEncoding (Remainder width) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod (wordEncoding width) (wordEncoding 1))
    (BinaryLabelEncoding.prod (lengthPairEncoding width)
      (BinaryLabelEncoding.prod (wordEncoding width.size) flagEncoding))

private theorem remainder_surjective (width : Nat) :
    Function.Surjective (remainderEncoding width).encode :=
  prod_surjective _ _ (prod_surjective _ _ (word_surjective _) (word_surjective _))
    (prod_surjective _ _ (prod_surjective _ _ (word_surjective _) (word_surjective _))
      (prod_surjective _ _ (word_surjective _)
        (prod_surjective _ _ (prod_surjective _ _ bool_surjective bool_surjective)
          (prod_surjective _ _ bool_surjective bool_surjective))))

/-- The complete native HRS carrier and its exact physical complement. -/
@[implicit_reducible]
def groupedEncoding (width : Nat) : BinaryLabelEncoding
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) × Remainder width) :=
  BinaryLabelEncoding.prod (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))
    (remainderEncoding width)

private theorem bridge_surjective (width : Nat) :
    Function.Surjective
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode := by
  have raw : Function.Surjective
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity (clockWidth width))
          (BinaryLabelEncoding.finIdentity (width + 3))) BinaryLabelEncoding.bool).encode :=
    prod_surjective _ _
      (prod_surjective _ _ Function.surjective_id Function.surjective_id)
      bool_surjective
  intro label
  obtain ⟨value, same⟩ := raw label
  refine ⟨(Addition.HRS.bridgeGrouping (width + 3) (clockWidth width)).symm value, ?_⟩
  change (BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity (clockWidth width))
      (BinaryLabelEncoding.finIdentity (width + 3))) BinaryLabelEncoding.bool).encode
        (Addition.HRS.bridgeGrouping (width + 3) (clockWidth width)
          ((Addition.HRS.bridgeGrouping (width + 3) (clockWidth width)).symm value)) = label
  rw [Equiv.apply_symm_apply]
  exact same

private theorem grouped_surjective (width : Nat) :
    Function.Surjective (groupedEncoding width).encode :=
  prod_surjective _ _ (bridge_surjective width) (remainder_surjective width)

private def groupedLabelEquiv (width : Nat) :
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) × Remainder width) ≃
      (Qubits (groupedEncoding width).width).Index :=
  Equiv.ofBijective (groupedEncoding width).encode
    ⟨(groupedEncoding width).encode_injective, grouped_surjective width⟩

private def registerLabelEquiv (width : Nat) :
    Registers width ≃ (Qubits (encoding width).width).Index :=
  Equiv.ofBijective (encoding width).encode
    ⟨(encoding width).encode_injective, encoding_surjective width⟩

/-- Decode the full actual product and reassemble every existing physical bit. -/
def indexEquiv (width : Nat) :
    (Qubits (groupedEncoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  (groupedLabelEquiv width).symm.trans
    ((grouping width).symm.trans (registerLabelEquiv width))

/-- The real field grouping agrees exactly with the complete basis-index transport. -/
theorem indexEquiv_encode (width : Nat) (state : Registers width) :
    indexEquiv width ((groupedEncoding width).encode (grouping width state)) =
      (encoding width).encode state := by
  change registerLabelEquiv width ((grouping width).symm
    ((groupedLabelEquiv width).symm (groupedLabelEquiv width (grouping width state)))) =
      registerLabelEquiv width state
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The full product contains exactly the original source-frame number of physical bits. -/
theorem grouped_width (width : Nat) :
    (groupedEncoding width).width =
      (clockWidth width + (width + 3) + 1) + (width + 1 + 3 * width.size + 4) := by
  change (clockWidth width + (width + 3) + 1) +
    ((width + 1) + ((width.size + width.size) + (width.size + ((1 + 1) + (1 + 1))))) = _
  omega

/-- Real physical positions of all unchanged Work1, length, and control coordinates. -/
def complementPhysicalIndex (width index : Nat) : Nat :=
  if index < width then index
  else if index = width then width + 2
  else if index < width + 1 + 3 * width.size then
    2 * (width + 3) + (index - (width + 1))
  else if index = width + 1 + 3 * width.size then 2 * (width + 3) + 4 * width.size
  else 2 * (width + 3) + 4 * width.size + 1 + (index - (width + 1 + 3 * width.size))

/-- Map every native and complementary slot onto its exact original-frame physical identity. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < clockWidth width + (width + 3) + 1 then
    ExtendedClockRegisters.physicalIndex width index
  else complementPhysicalIndex width (index - (clockWidth width + (width + 3) + 1))

private theorem focus_injective (width : Nat) :
    Function.Injective (fun index : Fin (clockWidth width + (width + 3) + 1) =>
      ExtendedClockRegisters.physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  change ExtendedClockRegisters.physicalIndex width left.val =
    ExtendedClockRegisters.physicalIndex width right.val at same
  unfold ExtendedClockRegisters.physicalIndex clockWidth at same
  unfold clockWidth at leftBound rightBound
  split_ifs at same <;> omega

private theorem complement_injective (width : Nat) :
    Function.Injective (fun index : Fin (width + 1 + 3 * width.size + 4) =>
      complementPhysicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  change complementPhysicalIndex width left.val = complementPhysicalIndex width right.val at same
  unfold complementPhysicalIndex at same
  split_ifs at same <;> omega

private theorem focus_ne_complement (width : Nat)
    (focus : Fin (clockWidth width + (width + 3) + 1))
    (rest : Fin (width + 1 + 3 * width.size + 4)) :
    ExtendedClockRegisters.physicalIndex width focus.val ≠
      complementPhysicalIndex width rest.val := by
  intro same
  have focusBound := focus.isLt
  have restBound := rest.isLt
  unfold clockWidth at focusBound
  unfold ExtendedClockRegisters.physicalIndex complementPhysicalIndex clockWidth at same
  split_ifs at same <;> omega

/-- No actual incrementer or spectator coordinate is merged by the complete physical map. -/
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
  by_cases leftFocus : left.val < clockWidth width + (width + 3) + 1
  · rw [if_pos leftFocus] at same
    by_cases rightFocus : right.val < clockWidth width + (width + 3) + 1
    · rw [if_pos rightFocus] at same
      exact congrArg (fun index : Fin (clockWidth width + (width + 3) + 1) => index.val)
        (focus_injective width (a₁ := ⟨left.val, leftFocus⟩) (a₂ := ⟨right.val, rightFocus⟩) same)
    · rw [if_neg rightFocus] at same
      exact False.elim (focus_ne_complement width ⟨left.val, leftFocus⟩
        ⟨right.val - (clockWidth width + (width + 3) + 1), by omega⟩ same)
  · rw [if_neg leftFocus] at same
    by_cases rightFocus : right.val < clockWidth width + (width + 3) + 1
    · rw [if_pos rightFocus] at same
      exact False.elim (focus_ne_complement width ⟨right.val, rightFocus⟩
        ⟨left.val - (clockWidth width + (width + 3) + 1), by omega⟩ same.symm)
    · rw [if_neg rightFocus] at same
      have values := congrArg
        (fun index : Fin (width + 1 + 3 * width.size + 4) => index.val)
        (complement_injective width
          (a₁ := ⟨left.val - (clockWidth width + (width + 3) + 1), by omega⟩)
          (a₂ := ⟨right.val - (clockWidth width + (width + 3) + 1), by omega⟩) same)
      change left.val - (clockWidth width + (width + 3) + 1) =
        right.val - (clockWidth width + (width + 3) + 1) at values
      omega

/-- Every native and complementary slot stays within the original complete frame. -/
theorem physicalIndex_within (width : Nat) (index : Fin (groupedEncoding width).width) :
    physicalIndex width index.val < (encoding width).width := by
  rw [encoding_width]
  have bound : index.val <
      (clockWidth width + (width + 3) + 1) + (width + 1 + 3 * width.size + 4) :=
    index.isLt.trans_le (grouped_width width).le
  unfold clockWidth at bound
  unfold physicalIndex ExtendedClockRegisters.physicalIndex complementPhysicalIndex clockWidth
  split_ifs <;> omega

/-- Every native and complementary bit has one valid original source address. -/
def wireMap (width : Nat) :
    Fin (groupedEncoding width).width → Fin (encoding width).width :=
  fun index => ⟨physicalIndex width index.val, physicalIndex_within width index⟩

theorem wireMap_injective (width : Nat) : Function.Injective (wireMap width) := by
  intro left right same
  exact physicalIndex_injective width (congrArg Fin.val same)

/-- The injective complete-frame map covers every original coordinate. -/
theorem wireMap_surjective (width : Nat) : Function.Surjective (wireMap width) := by
  have sameWidth : (groupedEncoding width).width = (encoding width).width := by
    rw [grouped_width, encoding_width]
    unfold clockWidth
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

/-- The retained HRS carrier and complement permute the complete original wire frame. -/
def wireEquiv (width : Nat) :
    Fin (groupedEncoding width).width ≃ Fin (encoding width).width :=
  Equiv.ofBijective (wireMap width)
    ⟨wireMap_injective width, wireMap_surjective width⟩

/-- The same original HRS target/work/control addresses are retained by the complete map. -/
theorem physicalIndex_focus (width : Nat)
    (index : Fin (clockWidth width + (width + 3) + 1)) :
    physicalIndex width index.val = ExtendedClockRegisters.physicalIndex width index.val :=
  if_pos index.isLt

/-- Concrete actual-word grouping and placement for the existing generic native-body transport. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (groupedEncoding width) (encoding width) :=
  EncodedBit.FullPlacement.ofWires (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)

/-- One borrowed Work2 bit at its actual big-endian grouped wire. -/
private def workBit (width : Nat) (index : Fin (width + 3)) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodLeftBit _ _
    (Addition.HRS.bridgeLowBit (width + 3) (clockWidth width) index.rev)

private theorem workBit_wire (width : Nat) (index : Fin (width + 3)) :
    (workBit width index).wire.val = clockWidth width + index.val := by
  change (Addition.HRS.bridgeLowBit (width + 3) (clockWidth width) index.rev).wire.val = _
  rw [Addition.HRS.hrsBridgeLowBit_wire, Fin.val_rev]
  have bound := index.isLt
  omega

private theorem workBit_get (width : Nat) (index : Fin (width + 3))
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (workBit width index).get state = state.1.1.1.val.testBit index.rev.val := by
  change (Addition.HRS.bridgeLowBit (width + 3) (clockWidth width) index.rev).get
    state.1 = _
  exact Addition.HRS.hrsBridgeLowBit_get _ _ index.rev state.1

/-- The strict placement reads each borrowed Work2 bit from its original Work2 wire. -/
theorem placement_work_bit (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    ((placement width).grouping state).1.1.1.val.testBit index.rev.val =
      state.secondWord.getMsbD index.val := by
  have same : wireEquiv width (workBit width index).wire =
      (secondWordBit width index).wire := by
    apply Fin.ext
    change physicalIndex width (workBit width index).wire.val =
      (secondWordBit width index).wire.val
    rw [workBit_wire]
    have inside : clockWidth width + index.val <
        clockWidth width + (width + 3) + 1 := by
      have bound := index.isLt
      omega
    rw [physicalIndex, if_pos inside,
      ExtendedClockRegisters.physicalIndex_work]
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (workBit width index) (secondWordBit width index) same state
  rw [workBit_get, secondWordBit_get] at actual
  exact actual

/-- One actual combined-clock bit at its grouped big-endian address. -/
private def clockBit (width : Nat) (index : Fin (clockWidth width)) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodLeftBit _ _
    (Addition.HRS.bridgeHighBit (width + 3) (clockWidth width) index.rev)

private theorem clockBit_wire (width : Nat) (index : Fin (clockWidth width)) :
    (clockBit width index).wire.val = index.val := by
  change (Addition.HRS.bridgeHighBit (width + 3) (clockWidth width) index.rev).wire.val = _
  rw [Addition.HRS.hrsBridgeHighBit_wire, Fin.val_rev]
  have bound := index.isLt
  omega

private theorem clockBit_get (width : Nat) (index : Fin (clockWidth width))
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (clockBit width index).get state = state.1.1.2.val.testBit index.rev.val := by
  change (Addition.HRS.bridgeHighBit (width + 3) (clockWidth width) index.rev).get
    state.1 = _
  exact Addition.HRS.hrsBridgeHighBit_get _ _ index.rev state.1

/-- The first two grouped clock positions read the existing high Work1 positions. -/
theorem placement_clock_high (width : Nat) (index : Fin 2)
    (state : Registers width) :
    (clockBit width ⟨index.val, by unfold clockWidth; have bound := index.isLt; omega⟩).get
        ((placement width).grouping state) =
      state.firstWord.getMsbD (width + index.val) := by
  let selected : Fin (clockWidth width) :=
    ⟨index.val, by unfold clockWidth; have bound := index.isLt; omega⟩
  let target := firstWordBit width
    ⟨width + index.val, by have bound := index.isLt; omega⟩
  have same : wireEquiv width (clockBit width selected).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (clockBit width selected).wire.val = target.wire.val
    rw [clockBit_wire]
    have inside : selected.val < clockWidth width + (width + 3) + 1 := by
      have bound := selected.isLt
      omega
    rw [physicalIndex, if_pos inside]
    exact ExtendedClockRegisters.physicalIndex_high width index
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (clockBit width selected) target same state
  simpa only [selected, placement, target, firstWordBit_get] using actual

/-- The remaining grouped clock positions read the original low shift register. -/
theorem placement_clock_low (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (clockBit width ⟨2 + index.val, by unfold clockWidth; have bound := index.isLt; omega⟩).get
        ((placement width).grouping state) =
      state.shift.getMsbD index.val := by
  let selected : Fin (clockWidth width) :=
    ⟨2 + index.val, by unfold clockWidth; have bound := index.isLt; omega⟩
  let target := shiftBit width index
  have same : wireEquiv width (clockBit width selected).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (clockBit width selected).wire.val = target.wire.val
    rw [clockBit_wire]
    have inside : selected.val < clockWidth width + (width + 3) + 1 := by
      have bound := selected.isLt
      omega
    rw [physicalIndex, if_pos inside]
    exact ExtendedClockRegisters.physicalIndex_low width index
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (clockBit width selected) target same state
  simpa only [selected, placement, target, shiftBit_get] using actual

/-- The HRS dirty-control position is the original Phase2 bit. -/
private def phaseBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodLeftBit _ _
    (Addition.HRS.bridgeDirtyBit (width + 3) (clockWidth width))

theorem placement_phase2 (width : Nat) (state : Registers width) :
    ((placement width).grouping state).1.2 = state.flags.second := by
  have same : wireEquiv width (phaseBit width).wire = (phase2Bit width).wire := by
    apply Fin.ext
    change physicalIndex width (phaseBit width).wire.val = (phase2Bit width).wire.val
    change physicalIndex width (clockWidth width + (width + 3)) = _
    have inside : clockWidth width + (width + 3) <
        clockWidth width + (width + 3) + 1 := by omega
    rw [physicalIndex, if_pos inside]
    exact ExtendedClockRegisters.physicalIndex_control width
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (phaseBit width) (phase2Bit width) same state
  change ((placement width).grouping state).1.2 = _ at actual
  simpa only [phase2Bit_get] using actual

/-- One retained main Work1 bit in the explicit complementary product. -/
private def mainBit (width : Nat) (index : Fin width) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodLeftBit _ _
      (BinaryLabelEncoding.prodLeftBit (wordEncoding width) (wordEncoding 1)
        (wordBit index)))

private theorem mainBit_wire (width : Nat) (index : Fin width) :
    (mainBit width index).wire.val =
      clockWidth width + (width + 3) + 1 + index.val := by
  rfl

private theorem mainBit_get (width : Nat) (index : Fin width)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (mainBit width index).get state = state.2.1.1.getMsbD index.val := by
  change (wordBit index).get state.2.1.1 = _
  exact wordBit_get index state.2.1.1

/-- The first Work1 segment remains on its exact original physical addresses. -/
theorem placement_main_bit (width : Nat) (index : Fin width)
    (state : Registers width) :
    (mainBit width index).get ((placement width).grouping state) =
      state.firstWord.getMsbD index.val := by
  let target := firstWordBit width ⟨index.val, by have bound := index.isLt; omega⟩
  have same : wireEquiv width (mainBit width index).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (mainBit width index).wire.val = target.wire.val
    rw [mainBit_wire]
    have outside : ¬clockWidth width + (width + 3) + 1 + index.val <
        clockWidth width + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    have beforeMain : index.val < width := index.isLt
    rw [complementPhysicalIndex, if_pos beforeMain]
    simpa only [target] using (firstWordBit_wire width ⟨index.val, by omega⟩).symm
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (mainBit width index) target same state
  simpa only [placement, target, firstWordBit_get] using actual

/-- The retained last Work1 bit follows the main segment in the complement. -/
private def lastBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodLeftBit _ _
      (BinaryLabelEncoding.prodRightBit (wordEncoding width) (wordEncoding 1)
        (wordBit (⟨0, by decide⟩ : Fin 1))))

private theorem lastBit_wire (width : Nat) :
    (lastBit width).wire.val = clockWidth width + (width + 3) + 1 + width := by
  rfl

private theorem lastBit_get (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (lastBit width).get state = state.2.1.2.getMsbD 0 := by
  change (wordBit (⟨0, by decide⟩ : Fin 1)).get state.2.1.2 = _
  exact wordBit_get (⟨0, by decide⟩ : Fin 1) state.2.1.2

/-- The last Work1 position remains the same original physical bit. -/
theorem placement_last_bit (width : Nat) (state : Registers width) :
    (lastBit width).get ((placement width).grouping state) =
      state.firstWord.getMsbD (width + 2) := by
  let target := firstWordBit width ⟨width + 2, by omega⟩
  have same : wireEquiv width (lastBit width).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (lastBit width).wire.val = target.wire.val
    rw [lastBit_wire]
    have outside : ¬clockWidth width + (width + 3) + 1 + width <
        clockWidth width + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    have notMain : ¬width < width := Nat.lt_irrefl width
    rw [complementPhysicalIndex, if_neg notMain, if_pos rfl]
    simpa only [target] using (firstWordBit_wire width ⟨width + 2, by omega⟩).symm
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (lastBit width) target same state
  simpa only [placement, target, firstWordBit_get] using actual

/-- The wire-derived placement retains exactly the source grouping's borrowed word. -/
theorem placement_grouping_work (width : Nat) (state : Registers width) :
    ((placement width).grouping state).1.1.1 = (grouping width state).1.1.1 := by
  apply (BinaryBasis.bigEndianEquiv (width + 3)).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  have actual := placement_work_bit width index state
  have expected : (grouping width state).1.1.1.val.testBit index.rev.val =
      state.secondWord.getMsbD index.val := by
    have within := index.isLt
    change state.secondWord.toNat.testBit index.rev.val =
      state.secondWord.getMsbD index.val
    rw [BitVec.getMsbD_eq_getLsbD]
    simp only [index.isLt, decide_true, Bool.true_and,
      BitVec.getLsbD, Fin.val_rev]
    rw [Nat.sub_sub]
    rw [Nat.add_comm index.val 1]
  exact actual.trans expected.symm

/-- The wire-derived placement has exactly the source's combined clock field. -/
theorem placement_grouping_clock (width : Nat) (state : Registers width) :
    ((placement width).grouping state).1.1.2 = (grouping width state).1.1.2 := by
  apply (BinaryBasis.bigEndianEquiv (clockWidth width)).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  have actual : ((placement width).grouping state).1.1.2.val.testBit index.rev.val =
      (clock state).getMsbD index.val := by
    by_cases high : index.val < 2
    · let selected : Fin 2 := ⟨index.val, high⟩
      have read := placement_clock_high width selected state
      rw [clockBit_get] at read
      have sameIndex :
          (⟨selected.val, by unfold clockWidth; have bound := selected.isLt; omega⟩ :
            Fin (clockWidth width)) = index := by
        apply Fin.ext
        rfl
      rw [sameIndex] at read
      have source := clock_bit width index state
      rw [if_pos high] at source
      exact read.trans source.symm
    · let selected : Fin width.size := ⟨index.val - 2, by
        have bound := index.isLt
        unfold clockWidth at bound
        omega⟩
      have read := placement_clock_low width selected state
      rw [clockBit_get] at read
      have sameIndex :
          (⟨2 + selected.val, by unfold clockWidth; have bound := selected.isLt; omega⟩ :
            Fin (clockWidth width)) = index := by
        apply Fin.ext
        dsimp only [selected]
        omega
      rw [sameIndex] at read
      have source := clock_bit width index state
      rw [if_neg high] at source
      have selectedVal : selected.val = index.val - 2 := rfl
      rw [selectedVal] at read
      exact read.trans source.symm
  have expected : (grouping width state).1.1.2.val.testBit index.rev.val =
      (clock state).getMsbD index.val := by
    change (clock state).toNat.testBit index.rev.val =
      (clock state).getMsbD index.val
    rw [BitVec.getMsbD_eq_getLsbD]
    simp only [index.isLt, decide_true, Bool.true_and,
      BitVec.getLsbD, Fin.val_rev]
    rw [Nat.sub_sub, Nat.add_comm index.val 1]
  exact actual.trans expected.symm

/-- The main Work1 projection agrees bit for bit with the exact source split. -/
theorem placement_grouping_main (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.1.1 = (grouping width state).2.1.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let selected : Fin width := ⟨index, within⟩
  have actual := placement_main_bit width selected state
  rw [mainBit_get] at actual
  have expected : (grouping width state).2.1.1.getMsbD index =
      state.firstWord.getMsbD index := by
    change (NumberTheory.SharedEEA.PaddingClock.main state.firstWord).getMsbD index = _
    exact (NumberTheory.SharedEEA.WordUnloading.main_bit state.firstWord index within).symm
  exact actual.trans expected.symm

/-- The final Work1 position agrees with the exact source split. -/
theorem placement_grouping_last (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.1.2 = (grouping width state).2.1.2 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have zero : index = 0 := by omega
  subst index
  have actual := placement_last_bit width state
  rw [lastBit_get] at actual
  have expected : (grouping width state).2.1.2.getMsbD 0 =
      state.firstWord.getMsbD (width + 2) := by
    change (NumberTheory.SharedEEA.PaddingClock.last state.firstWord).getMsbD 0 = _
    have reassembled := NumberTheory.SharedEEA.WordUnloading.reassemble state.firstWord
    have indexed := congrArg
      (fun word : BitVec (width + 3) => word.getMsbD (width + 2)) reassembled
    simpa only [BitVec.getMsbD_append, if_pos (le_refl (width + 2)),
      Nat.sub_self] using indexed
  exact actual.trans expected.symm

/-- Lift a retained coefficient/quotient length bit through the full complement. -/
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
      clockWidth width + (width + 3) + 1 + (width + 1 + index.val) := by
  rfl

private theorem coefficientBit_get (width : Nat) (index : Fin width.size)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (coefficientBit width index).get state = state.2.2.1.1.getMsbD index.val := by
  change (wordBit index).get state.2.2.1.1 = _
  exact wordBit_get index state.2.2.1.1

/-- The coefficient length is read at its existing original source wires. -/
theorem placement_coefficient_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (coefficientBit width index).get ((placement width).grouping state) =
      state.coefficientLength.getMsbD index.val := by
  let target := coefficientLengthBit width index
  have same : wireEquiv width (coefficientBit width index).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (coefficientBit width index).wire.val = target.wire.val
    rw [coefficientBit_wire, coefficientLengthBit_wire]
    have outside : ¬clockWidth width + (width + 3) + 1 + (width + 1 + index.val) <
        clockWidth width + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    unfold complementPhysicalIndex
    have bound := index.isLt
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (coefficientBit width index) target same state
  simpa only [placement, target, coefficientLengthBit_get] using actual

/-- The retained quotient-length word follows the coefficient-length word. -/
private def quotientBit (width : Nat) (index : Fin width.size) :
    EncodedBit (groupedEncoding width) :=
  lengthPairBit width
    (BinaryLabelEncoding.prodRightBit (wordEncoding width.size) (wordEncoding width.size)
      (wordBit index))

private theorem quotientBit_wire (width : Nat) (index : Fin width.size) :
    (quotientBit width index).wire.val =
      clockWidth width + (width + 3) + 1 + (width + 1 + width.size + index.val) := by
  change (clockWidth width + (width + 3) + 1) +
    (width + 1 + (width.size + index.val)) = _
  omega

private theorem quotientBit_get (width : Nat) (index : Fin width.size)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (quotientBit width index).get state = state.2.2.1.2.getMsbD index.val := by
  change (wordBit index).get state.2.2.1.2 = _
  exact wordBit_get index state.2.2.1.2

/-- The quotient length is read at its existing original source wires. -/
theorem placement_quotient_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (quotientBit width index).get ((placement width).grouping state) =
      state.quotientLength.getMsbD index.val := by
  let target := quotientLengthBit width index
  have same : wireEquiv width (quotientBit width index).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (quotientBit width index).wire.val = target.wire.val
    rw [quotientBit_wire, quotientLengthBit_wire]
    have outside : ¬clockWidth width + (width + 3) + 1 +
        (width + 1 + width.size + index.val) <
        clockWidth width + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    unfold complementPhysicalIndex
    have bound := index.isLt
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (quotientBit width index) target same state
  simpa only [placement, target, quotientLengthBit_get] using actual

/-- The third retained length word is the original divisor-length field. -/
private def divisorBit (width : Nat) (index : Fin width.size) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodLeftBit (wordEncoding width.size) flagEncoding
          (wordBit index))))

private theorem divisorBit_wire (width : Nat) (index : Fin width.size) :
    (divisorBit width index).wire.val = clockWidth width + (width + 3) + 1 +
      (width + 1 + 2 * width.size + index.val) := by
  change (clockWidth width + (width + 3) + 1) +
    (width + 1 + ((width.size + width.size) + index.val)) = _
  omega

private theorem divisorBit_get (width : Nat) (index : Fin width.size)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) ×
      Remainder width) :
    (divisorBit width index).get state = state.2.2.2.1.getMsbD index.val := by
  change (wordBit index).get state.2.2.2.1 = _
  exact wordBit_get index state.2.2.2.1

/-- The divisor length is read at its existing original source wires. -/
theorem placement_divisor_bit (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (divisorBit width index).get ((placement width).grouping state) =
      state.divisorLength.getMsbD index.val := by
  let target := divisorLengthBit width index
  have same : wireEquiv width (divisorBit width index).wire = target.wire := by
    apply Fin.ext
    change physicalIndex width (divisorBit width index).wire.val = target.wire.val
    rw [divisorBit_wire, divisorLengthBit_wire]
    have outside : ¬clockWidth width + (width + 3) + 1 +
        (width + 1 + 2 * width.size + index.val) <
        clockWidth width + (width + 3) + 1 := by omega
    rw [physicalIndex, if_neg outside]
    simp only [Nat.add_sub_cancel_left]
    unfold complementPhysicalIndex
    have bound := index.isLt
    split_ifs <;> omega
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (divisorBit width index) target same state
  simpa only [placement, target, divisorLengthBit_get] using actual

/-- The retained length words are the exact coefficient, quotient and divisor fields. -/
theorem placement_grouping_lengths (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.1 = (grouping width state).2.2.1 ∧
      ((placement width).grouping state).2.2.2.1 = (grouping width state).2.2.2.1 := by
  constructor
  · apply Prod.ext
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      let selected : Fin width.size := ⟨index, within⟩
      have actual := placement_coefficient_bit width selected state
      rw [coefficientBit_get] at actual
      exact actual
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      let selected : Fin width.size := ⟨index, within⟩
      have actual := placement_quotient_bit width selected state
      rw [quotientBit_get] at actual
      exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := placement_divisor_bit width selected state
    rw [divisorBit_get] at actual
    exact actual

/-- Lift any of the four retained flags through the same complete complement. -/
private def retainedFlagBit (width : Nat) (bit : EncodedBit flagEncoding) :
    EncodedBit (groupedEncoding width) :=
  BinaryLabelEncoding.prodRightBit _ _
    (BinaryLabelEncoding.prodRightBit _ _
      (BinaryLabelEncoding.prodRightBit _ _
        (BinaryLabelEncoding.prodRightBit (wordEncoding width.size) flagEncoding bit)))

private theorem retainedFlagBit_wire (width : Nat) (bit : EncodedBit flagEncoding) :
    (retainedFlagBit width bit).wire.val = clockWidth width + (width + 3) + 1 +
      (width + 1 + 3 * width.size + bit.wire.val) := by
  change (clockWidth width + (width + 3) + 1) +
    (width + 1 + ((width.size + width.size) + (width.size + bit.wire.val))) = _
  omega

/-- The four retained flags skip only the original Phase2 wire. -/
private theorem retainedFlagBit_physical (width : Nat) (bit : EncodedBit flagEncoding) :
    physicalIndex width (retainedFlagBit width bit).wire.val =
      if bit.wire.val = 0 then 2 * (width + 3) + 4 * width.size
      else 2 * (width + 3) + 4 * width.size + 1 + bit.wire.val := by
  rw [retainedFlagBit_wire]
  have outside : ¬clockWidth width + (width + 3) + 1 +
      (width + 1 + 3 * width.size + bit.wire.val) <
      clockWidth width + (width + 3) + 1 := by omega
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

/-- The retained Phase1 control is read from its original source address. -/
theorem placement_phase1 (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.1.1 = state.flags.first := by
  have same : wireEquiv width (firstFlagBit width).wire = (phase1Bit width).wire := by
    apply Fin.ext
    change physicalIndex width (firstFlagBit width).wire.val = (phase1Bit width).wire.val
    unfold firstFlagBit
    rw [retainedFlagBit_physical, phase1Bit_wire]
    rfl
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (firstFlagBit width) (phase1Bit width) same state
  change ((placement width).grouping state).2.2.2.2.1.1 =
    (phase1Bit width).get state at actual
  simpa only [phase1Bit_get] using actual

private def signFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodLeftBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

/-- The retained Sign bit skips Phase2 and reads its original source address. -/
theorem placement_sign (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.1.2 = state.flags.sign := by
  have same : wireEquiv width (signFlagBit width).wire = (signBit width).wire := by
    apply Fin.ext
    change physicalIndex width (signFlagBit width).wire.val = (signBit width).wire.val
    unfold signFlagBit
    rw [retainedFlagBit_physical, signBit_wire]
    rfl
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (signFlagBit width) (signBit width) same state
  change ((placement width).grouping state).2.2.2.2.1.2 =
    (signBit width).get state at actual
  simpa only [signBit_get] using actual

private def iterationFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodRightBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

/-- The borrowed Iter bit is retained at its original source address. -/
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
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (iterationFlagBit width) (iterationBit width) same state
  change ((placement width).grouping state).2.2.2.2.2.1 =
    (iterationBit width).get state at actual
  simpa only [iterationBit_get] using actual

private def controlFlagBit (width : Nat) : EncodedBit (groupedEncoding width) :=
  retainedFlagBit width
    (BinaryLabelEncoding.prodRightBit flagPairEncoding flagPairEncoding
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

/-- The retained Ctrl bit remains at its original source address. -/
theorem placement_control (width : Nat) (state : Registers width) :
    ((placement width).grouping state).2.2.2.2.2.2 = state.control := by
  have same : wireEquiv width (controlFlagBit width).wire = (controlBit width).wire := by
    apply Fin.ext
    change physicalIndex width (controlFlagBit width).wire.val = (controlBit width).wire.val
    unfold controlFlagBit
    rw [retainedFlagBit_physical, controlBit_wire]
    rfl
  have actual := EncodedBit.FullPlacement.ofWires_read
    (groupedEncoding width) (encoding width)
    (grouped_surjective width) (encoding_surjective width) (wireEquiv width)
    (controlFlagBit width) (controlBit width) same state
  change ((placement width).grouping state).2.2.2.2.2.2 =
    (controlBit width).get state at actual
  simpa only [controlBit_get] using actual

/-- Every physical wire and every source-level field belong to the same exact regrouping. -/
theorem placement_grouping (width : Nat) (state : Registers width) :
    (placement width).grouping state = grouping width state := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · exact placement_grouping_work width state
      · exact placement_grouping_clock width state
    · exact placement_phase2 width state
  · apply Prod.ext
    · apply Prod.ext
      · exact placement_grouping_main width state
      · exact placement_grouping_last width state
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

/-- The strict wire-derived placement has exactly the registered source field equivalence. -/
theorem placement_grouping_eq (width : Nat) :
    (placement width).grouping = grouping width := by
  apply Equiv.ext
  exact placement_grouping width

end

end QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockPlacement
