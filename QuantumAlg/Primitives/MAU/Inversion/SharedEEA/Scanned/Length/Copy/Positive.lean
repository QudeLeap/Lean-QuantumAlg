/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Bit
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Components.Encoded.BitGates.ConditionalListLaws
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor

/-! # Complete actual selected word XOR with original arbitrary dirty Iter -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates

/-- Low prefix bits and original arbitrary length output use the same little-endian order. -/
def source (width : Nat) : Word (encoding width) width.size := ⟨dataBit width⟩

/-- Original length output without any zero-initialization promise. -/
def target (width : Nat) (field : Field) : Word (encoding width) width.size :=
  ⟨targetBit width field⟩

private lemma source_target (width : Nat) (field : Field) (bit : Fin width.size) :
    ((source width).bit bit).wire ≠ ((target width field).bit bit).wire :=
  (source_prefix_ne width _ _).symm

private def selectedWord (width : Nat) (poolFlag : Bool) (state : Data width) : Bool :=
  (active width poolFlag).get state && (conjunctionBit width).get state

private def originalBit (width : Nat) (field : Field) (bit : Fin width.size) :
    List (GateSpec (encoding width)) :=
  [.cnot (dataBit width bit) (targetBit width field bit) (source_target width field bit)]

private lemma bit_if (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size)
    (state : Data width) :
    GateSpec.stepList (bitGates width poolFlag field bit) state =
      if selectedWord width poolFlag state then
        GateSpec.stepList (originalBit width field bit) state else state := by
  rw [bitGates_step]
  simp only [originalBit, GateSpec.stepList, GateSpec.step, id_eq, cnotStep, selectedWord]
  cases (active width poolFlag).get state <;> cases (conjunctionBit width).get state <;> rfl

private lemma original_retained (width : Nat) (poolFlag : Bool) (field : Field)
    (bit : Fin width.size) (state : Data width) :
    selectedWord width poolFlag (GateSpec.stepList (originalBit width field bit) state) =
      selectedWord width poolFlag state := by
  simp only [originalBit, GateSpec.stepList, GateSpec.step, id_eq, selectedWord]
  rw [cnotStep_get_of_target_ne (dataBit width bit) (targetBit width field bit)
      (active width poolFlag) (active_target width poolFlag field bit).symm,
    cnotStep_get_of_target_ne (dataBit width bit) (targetBit width field bit)
      (conjunctionBit width) (source_conjunction_ne width _)]

/-- Every output bit emits its real four-Toffoli word on the same existing physical carrier. -/
def positiveGates (width : Nat) (poolFlag : Bool) (field : Field) :
    List (GateSpec (encoding width)) :=
  (List.finRange width.size).flatMap (bitGates width poolFlag field)

/-- The full native word has exactly the selected XOR action on every original physical label. -/
lemma positiveGates_step (width : Nat) (poolFlag : Bool) (field : Field) (state : Data width) :
    GateSpec.stepList (positiveGates width poolFlag field) state =
      if selectedWord width poolFlag state then
        Word.xorIntoStep (source width) (target width field) (source_target width field) state
      else state := by
  have actual := GateSpec.stepList_flatMap_if
    (fun value => selectedWord width poolFlag value = true)
    (originalBit width field) (bitGates width poolFlag field)
    (bit_if width poolFlag field)
    (fun bit value => by rw [original_retained]) (List.finRange width.size) state
  have original : (List.finRange width.size).flatMap (originalBit width field) =
      Word.xorIntoGates (source width) (target width field) (source_target width field) := by
    change (List.finRange width.size).flatMap
      (fun bit => [GateSpec.cnot (dataBit width bit) (targetBit width field bit)
        (source_target width field bit)]) =
      List.ofFn (fun bit => GateSpec.cnot (dataBit width bit) (targetBit width field bit)
        (source_target width field bit))
    rw [← List.map_eq_flatMap, List.ofFn_eq_map]
  rw [original] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
