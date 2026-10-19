/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Complement
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small.BiFlip
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Product
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Small

/-!
# Actual native control of the arithmetic bi-flip

The body subtracts the pivot with HRS addition and complements the target
[G17, paper.tex:276-277]. A control expands each actual X/CNOT/Toffoli into
native gates. A controlled Toffoli temporarily borrows an existing unused
wire and restores it before the next source gate. The fixed zero-, one- and
two-bit bases use explicit X/CNOT lists, so no extra storage is needed there.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec

/-- The finite arithmetic action agrees with the complement of the negative offset. -/
lemma gidneyBiFlipWord_eq_offset_complement (width : Nat)
    (pivot : Fin (2 ^ width + 1)) (input : Fin (2 ^ width)) :
    HRS.complementWord (HRS.addWord (negatedPivot width pivot.val) input) =
      biFlipWordOutput pivot input := by
  apply Fin.ext
  exact (Nat.FixedWidth.biFlip_eq_complement_sub_mod
    (by have := pivot.isLt; omega) input.isLt).symm

/-- Independent body action, with the arbitrary helper returned exactly. -/
def biFlipBodyOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : HRS.OneDirtyRegisters width) : HRS.OneDirtyRegisters width :=
  (biFlipWordOutput pivot state.1, state.2)

/-- The original flag selects the bi-flip, and both borrowed bits are preserved. -/
def biFlipOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Registers width) : Registers width :=
  (state.1, (if state.1 then biFlipWordOutput pivot state.2.1 else state.2.1, state.2.2))

/- Target-only complement placed beside the existing helper. -/
private def complementBodyGates (width : Nat) : List (GateSpec (HRS.oneDirtyEncoding width)) :=
  (complementGates width).map (GateSpec.prodLeft bool)

/-- Actual negative-offset and complement instructions before adding the control. -/
def biFlipBodyGates (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    List (GateSpec (HRS.oneDirtyEncoding width)) :=
  HRS.oneDirtyGates width (negatedPivot width pivot.val) ++ complementBodyGates width

/-- The literal arithmetic body restores the helper on every joint input. -/
lemma gidneyBiFlipBodyGates_step (width : Nat) (pivot : Fin (2 ^ width + 1))
    (state : HRS.OneDirtyRegisters width) :
    stepList (biFlipBodyGates width pivot) state = biFlipBodyOutput pivot state := by
  rw [biFlipBodyGates, stepList_append, HRS.hrsOneDirtyGates_step]
  exact (stepList_prodLeft bool (complementGates width) (HRS.oneDirtyOutput _ state)).trans
    (congrArg (fun word => (word, state.2))
      ((gidneyComplement_step width _).trans
        (gidneyBiFlipWord_eq_offset_complement width pivot state.1)))

private lemma singleBit_wire (position : Fin bool.width) : boolBit.wire = position := by
  apply Fin.ext
  have bound : position.val < 1 := position.isLt
  change 0 = position.val
  omega

/-- The complete physical bit family of the word and its helper. -/
def oneDirtyBits (width : Nat) : Fin (HRS.oneDirtyEncoding width).width →
    EncodedBit (HRS.oneDirtyEncoding width) :=
  productBit (finIdentityBit width) (fun _ => boolBit)

/-- Every physical position has its corresponding bit lens. -/
lemma gidneyOneDirtyBits_wire (width : Nat) (position : Fin (HRS.oneDirtyEncoding width).width) :
    (oneDirtyBits width position).wire = position := by
  exact productBit_wire (left := finIdentity width) (right := bool)
    (finIdentityBit width) (fun _ => boolBit)
    (fun _ => rfl) singleBit_wire position

private def smallGrouping (width : Nat) : Registers width ≃ (Bool × Fin (2 ^ width)) × Bool :=
  (Equiv.prodAssoc Bool (Fin (2 ^ width)) Bool).symm

private def smallPlacement (width : Nat) :
    FullPlacement (prod (prod bool (finIdentity width)) bool) (encoding width) :=
  FullPlacement.ofEqualWidth _ _ (smallGrouping width)
    (by change (1 + width) + 1 = 1 + (width + 1); omega)
    (by
      intro state
      apply Fin.ext
      change (bool.encode state.2.2).val +
          2 ^ 1 * (state.2.1.val + 2 ^ width * (bool.encode state.1).val) =
        (bool.encode state.2.2).val + 2 ^ 1 * state.2.1.val +
          2 ^ (width + 1) * (bool.encode state.1).val
      simp only [pow_add, pow_one]
      ring)

private def smallBiFlipGates (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) : List (GateSpec (encoding width)) :=
  (((Small.biFlipGates width small pivot).map (controlSmall boolBit small)).map
    (GateSpec.prodLeft bool)).map (smallPlacement width).placeGate

private lemma smallBiFlipGates_step (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) (state : Registers width) :
    stepList (smallBiFlipGates width small pivot) state = biFlipOutput pivot state := by
  have lifted := stepList_prodLeft bool
    ((Small.biFlipGates width small pivot).map (controlSmall boolBit small))
    (smallGrouping width state)
  have controlled := controlSmallList_step boolBit small
    (Small.biFlipGates width small pivot) (state.1, state.2.1)
  calc
    _ = (smallGrouping width).symm
        (stepList (((Small.biFlipGates width small pivot).map
          (controlSmall boolBit small)).map (GateSpec.prodLeft bool))
          (smallGrouping width state)) := by
      rw [smallBiFlipGates, FullPlacement.placeGates_step]
      simp only [FullPlacement.step, smallPlacement, FullPlacement.ofEqualWidth_grouping]
    _ = (smallGrouping width).symm
        (stepList ((Small.biFlipGates width small pivot).map (controlSmall boolBit small))
          (state.1, state.2.1), state.2.2) := congrArg (smallGrouping width).symm lifted
    _ = _ := by
      rw [controlled, Small.biFlipGates_step]
      rfl

private def largeBiFlipGates (width : Nat) (large : 3 ≤ width)
    (pivot : Fin (2 ^ width + 1)) : List (GateSpec (encoding width)) :=
  controlRightList (fun _ => boolBit) (oneDirtyBits width)
    singleBit_wire (gidneyOneDirtyBits_wire width)
    (by change 5 ≤ 1 + (width + 1); omega) boolBit (biFlipBodyGates width pivot)

private lemma largeBiFlipGates_step (width : Nat) (large : 3 ≤ width)
    (pivot : Fin (2 ^ width + 1)) (state : Registers width) :
    stepList (largeBiFlipGates width large pivot) state = biFlipOutput pivot state := by
  have actual := controlRightList_step (fun _ => boolBit) (oneDirtyBits width)
    singleBit_wire (gidneyOneDirtyBits_wire width)
    (by change 5 ≤ 1 + (width + 1); omega) boolBit (biFlipBodyGates width pivot) state
  rw [gidneyBiFlipBodyGates_step] at actual
  apply actual.trans
  rcases state with ⟨flag, word, helper⟩
  cases flag <;> rfl

/-- Native bi-flip instructions on the original flag, word and helper carrier. -/
def biFlipGates (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    List (GateSpec (encoding width)) :=
  if small : width ≤ 2 then smallBiFlipGates width small pivot
  else largeBiFlipGates width (by omega) pivot

/-- Exact conditional action, with no phase relaxation and no fresh work wire. -/
lemma gidneyBiFlipGates_step (width : Nat) (pivot : Fin (2 ^ width + 1))
    (state : Registers width) :
    stepList (biFlipGates width pivot) state = biFlipOutput pivot state := by
  unfold biFlipGates
  split
  · exact smallBiFlipGates_step width _ pivot state
  · exact largeBiFlipGates_step width _ pivot state

/-- Emit the actual CNOT/Toffoli expansion on the complete fixed carrier. -/
def biFlipProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (biFlipGates width pivot)

/-- The actual native expansion implements the complete coherent bi-flip contract. -/
lemma gidneyBiFlip_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (biFlipProgram width pivot)
      environment (biFlipOutput pivot) :=
  realizesList_congrStep _ _ _ (gidneyBiFlipGates_step width pivot) environment

/-- The interface remains exactly the original target word and two arbitrary bits. -/
lemma gidneyBiFlip_interface (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (encoding width).width = width + 2 ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (width + 2) :=
  gidneyPackedOffset_interface width (extendedNegatedPivot width pivot.val)

/-- Actual events come only from the emitted literal expansion. -/
lemma gidneyBiFlip_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).eventCost =
      ResourcePool.ofList ((biFlipGates width pivot).map (event .empty)) :=
  programList_eventCost _ _ _

/-- A coarse independent bound accounts for every expanded source gate and the small bases. -/
lemma gidneyBiFlipGates_length_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipGates width pivot).length ≤
      4 * (width * (39 * Nat.clog 2 width + 1) + width) + 2 := by
  unfold biFlipGates
  split
  · have bound := Small.biFlipGates_length width (by assumption) pivot
    simp only [smallBiFlipGates, List.length_map]
    omega
  · have bound := controlRightList_length_bound
      (fun _ => boolBit) (oneDirtyBits width)
      singleBit_wire (gidneyOneDirtyBits_wire width)
      (by change 5 ≤ 1 + (width + 1); omega) boolBit (biFlipBodyGates width pivot)
    have hrsBound := HRS.hrsOneDirtyGates_length_bound width (negatedPivot width pivot.val)
    have complementLength : (complementBodyGates width).length = width :=
      (List.length_map (as := complementGates width) (f := GateSpec.prodLeft bool)).trans
        List.length_ofFn
    calc
      _ ≤ 4 * (biFlipBodyGates width pivot).length := bound
      _ ≤ _ := by
        rw [biFlipBodyGates, List.length_append, complementLength]
        omega

end

end QuantumAlg.MAU.Addition.Gidney
