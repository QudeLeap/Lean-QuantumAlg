/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Registers
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

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

private theorem grouped_surjective (width : Nat) :
    Function.Surjective (groupedEncoding width).encode :=
  prod_surjective _ _
    (prod_surjective _ _ (prod_surjective _ _ Function.surjective_id Function.surjective_id)
      bool_surjective)
    (remainder_surjective width)

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
      (width + 3 + clockWidth width + 1) + (width + 1 + 3 * width.size + 4) := by
  change (width + 3 + clockWidth width + 1) +
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
  if index < width + 3 + clockWidth width + 1 then
    ExtendedClockRegisters.physicalIndex width index
  else complementPhysicalIndex width (index - (width + 3 + clockWidth width + 1))

private theorem focus_injective (width : Nat) :
    Function.Injective (fun index : Fin (width + 3 + clockWidth width + 1) =>
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
    (focus : Fin (width + 3 + clockWidth width + 1))
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
  by_cases leftFocus : left.val < width + 3 + clockWidth width + 1
  · rw [if_pos leftFocus] at same
    by_cases rightFocus : right.val < width + 3 + clockWidth width + 1
    · rw [if_pos rightFocus] at same
      exact congrArg (fun index : Fin (width + 3 + clockWidth width + 1) => index.val)
        (focus_injective width (a₁ := ⟨left.val, leftFocus⟩) (a₂ := ⟨right.val, rightFocus⟩) same)
    · rw [if_neg rightFocus] at same
      exact False.elim (focus_ne_complement width ⟨left.val, leftFocus⟩
        ⟨right.val - (width + 3 + clockWidth width + 1), by omega⟩ same)
  · rw [if_neg leftFocus] at same
    by_cases rightFocus : right.val < width + 3 + clockWidth width + 1
    · rw [if_pos rightFocus] at same
      exact False.elim (focus_ne_complement width ⟨right.val, rightFocus⟩
        ⟨left.val - (width + 3 + clockWidth width + 1), by omega⟩ same.symm)
    · rw [if_neg rightFocus] at same
      have values := congrArg
        (fun index : Fin (width + 1 + 3 * width.size + 4) => index.val)
        (complement_injective width
          (a₁ := ⟨left.val - (width + 3 + clockWidth width + 1), by omega⟩)
          (a₂ := ⟨right.val - (width + 3 + clockWidth width + 1), by omega⟩) same)
      change left.val - (width + 3 + clockWidth width + 1) =
        right.val - (width + 3 + clockWidth width + 1) at values
      omega

/-- Every native and complementary slot stays within the original complete frame. -/
theorem physicalIndex_within (width : Nat) (index : Fin (groupedEncoding width).width) :
    physicalIndex width index.val < (encoding width).width := by
  rw [encoding_width]
  have bound : index.val <
      (width + 3 + clockWidth width + 1) + (width + 1 + 3 * width.size + 4) :=
    index.isLt.trans_le (grouped_width width).le
  unfold clockWidth at bound
  unfold physicalIndex ExtendedClockRegisters.physicalIndex complementPhysicalIndex clockWidth
  split_ifs <;> omega

/-- The same original HRS target/work/control addresses are retained by the complete map. -/
theorem physicalIndex_focus (width : Nat)
    (index : Fin (width + 3 + clockWidth width + 1)) :
    physicalIndex width index.val = ExtendedClockRegisters.physicalIndex width index.val :=
  if_pos index.isLt

/-- Concrete actual-word grouping and placement for the existing generic native-body transport. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (groupedEncoding width) (encoding width) where
  grouping := ExtendedClockRegisters.grouping width
  basis := indexEquiv width
  basis_encode := indexEquiv_encode width
  physicalIndex := physicalIndex width
  wire_injective := physicalIndex_injective width
  wire_within := physicalIndex_within width

end

end QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockPlacement
