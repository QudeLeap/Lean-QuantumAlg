/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift

/-!
# Actual target rotation on the original two-word arithmetic frame

The cyclic shift is a literal sweep of adjacent CNOT swaps. It retains
the entire quantum source word and the incoming flag, with no clean-bit
assumption. Its inverse is the complete native list in reverse order.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma adjacent_rotation_readout {Data : Type} {binary : BinaryLabelEncoding Data}
    {size : Nat} (word : EncodedBit.Word binary size)
    (separate : ∀ left right : Fin size, left ≠ right →
      (word.bit left).wire ≠ (word.bit right).wire)
    (large : 2 ≤ size) (readout : Data → BitVec size)
    (read : ∀ index state, (word.bit index).get state = (readout state).getMsbD index.val)
    (state : Data) :
    readout (word.adjacentShiftLeftStep separate state) = (readout state).rotateLeft 1 := by
  let : NeZero size := ⟨by omega⟩
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have entry := EncodedBit.Word.adjacentShiftLeftStep_get_indexPerm
    word separate ⟨index, within⟩ state
  rw [EncodedBit.Word.adjacentSwapIndexPerm_ofFn_eq_finRotate, read, read] at entry
  have position : (finRotate size ⟨index, within⟩).val = (1 + index) % size := by
    rw [finRotate_apply, Fin.val_add]
    have one : (1 : Fin size).val = 1 := by
      change 1 % size = 1
      exact Nat.mod_eq_of_lt (by omega)
    change (index + (1 : Fin size).val) % size = _
    rw [one, Nat.add_comm index 1]
  rw [position] at entry
  simpa only [BitVec.getMsbD_rotateLeft, within, decide_true, Bool.true_and] using entry

local instance : NeZero width := ⟨by decide⟩

private def reversedIndex (index : Fin width) : Fin width :=
  ⟨width - 1 - index.val, by have bounded := index.isLt; omega⟩

/-- The original target in physical most-significant-first order. -/
def targetWord : EncodedBit.Word encoding width :=
  ⟨fun index => targetBit (reversedIndex index)⟩

private lemma targetWord_distinct (left right : Fin width) (different : left ≠ right) :
    (targetWord.bit left).wire ≠ (targetWord.bit right).wire := by
  apply MAU.Addition.TTK.ttkWithOverflowBit_disjoint
  apply MAU.Addition.TTK.ttkRightRight_disjoint
  intro same
  apply different
  apply Fin.ext
  have positions := congrArg Fin.val same
  have leftBound := left.isLt
  have rightBound := right.isLt
  dsimp only [reversedIndex] at positions
  omega

private lemma targetWord_get (index : Fin width) (state : Registers) :
    (targetWord.bit index).get state = (BitVec.ofFin (w := width) state.1.2).getMsbD index.val := by
  simp only [targetWord, targetBit, MAU.Addition.TTK.ttkWithOverflowBit_get,
    MAU.Addition.TTK.ttkRightBit_get, reversedIndex,
    BitVec.getMsbD_eq_getLsbD, index.isLt, decide_true, Bool.true_and, BitVec.getLsbD]
  rfl

/-- One actual cyclic target rotation, compiled solely from existing-wire CNOTs. -/
def rotationGates : List (GateSpec encoding) :=
  EncodedBit.Word.adjacentShiftLeftGates targetWord targetWord_distinct

/-- Every restoration instruction is retained in the exact native inverse. -/
def inverseRotationGates : List (GateSpec encoding) := rotationGates.reverse

def rotationProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty rotationGates

private def withoutTarget (state : Registers) : Registers := ((state.1.1, 0), state.2)

private lemma withoutTarget_cnot (left right : Fin width) (state : Registers) :
    withoutTarget (cnotStep (targetWord.bit left) (targetWord.bit right) state) =
      withoutTarget state := by
  unfold cnotStep
  split <;> rfl

private lemma withoutTarget_swap (index : Fin (width - 1)) (state : Registers) :
    withoutTarget (stepList
      (EncodedBit.Word.adjacentSwapGates targetWord targetWord_distinct index) state) =
      withoutTarget state := by
  simp only [EncodedBit.Word.adjacentSwapGates, swapGates, stepList, step,
    id_eq, withoutTarget_cnot]

private lemma withoutTarget_indices (indices : List (Fin (width - 1))) (state : Registers) :
    withoutTarget (stepList
      (indices.flatMap (EncodedBit.Word.adjacentSwapGates targetWord targetWord_distinct))
      state) = withoutTarget state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      rw [List.flatMap_cons, stepList_append, ih, withoutTarget_swap]

private lemma rotation_complement (state : Registers) :
    withoutTarget (stepList rotationGates state) = withoutTarget state :=
  withoutTarget_indices (List.ofFn fun index : Fin (width - 1) => index) state

private lemma rotation_source (first second : Registers)
    (same : withoutTarget first = withoutTarget second) : first.1.1 = second.1.1 := by
  have projected : (withoutTarget first).1.1 = (withoutTarget second).1.1 :=
    congrArg (fun state : Registers => state.1.1) same
  exact projected

private lemma rotation_flag (first second : Registers)
    (same : withoutTarget first = withoutTarget second) : first.2 = second.2 := by
  have projected : (withoutTarget first).2 = (withoutTarget second).2 :=
    congrArg (fun state : Registers => state.2) same
  exact projected

private lemma rotation_coordinates_eq {First Second Third : Type}
    {first second : (First × Second) × Third}
    (left : first.1.1 = second.1.1) (right : first.1.2 = second.1.2)
    (flag : first.2 = second.2) : first = second :=
  Prod.ext (Prod.ext left right) flag

private lemma readout_fin_eq {size : Nat} (first : Fin (2 ^ size)) (second : BitVec size)
    (same : BitVec.ofFin first = second) : first = second.toFin :=
  congrArg BitVec.toFin same

private lemma rotation_step_function :
    stepList rotationGates = targetWord.adjacentShiftLeftStep targetWord_distinct := by
  unfold rotationGates EncodedBit.Word.adjacentShiftLeftStep
  rfl

section

-- Readout proofs use the certified native-list laws rather than evaluating the actual sweep.
attribute [local irreducible] GateSpec.stepList

private lemma rotation_target (state : Registers) :
    BitVec.ofFin (w := width) (stepList rotationGates state).1.2 =
      (BitVec.ofFin (w := width) state.1.2).rotateLeft 1 := by
  have native : BitVec.ofFin (w := width) (stepList rotationGates state).1.2 =
      BitVec.ofFin (w := width)
        (targetWord.adjacentShiftLeftStep targetWord_distinct state).1.2 :=
    congrArg (fun action : Registers → Registers =>
      BitVec.ofFin (w := width) (action state).1.2) rotation_step_function
  exact native.trans (adjacent_rotation_readout targetWord targetWord_distinct (by decide)
    (fun value : Registers => BitVec.ofFin (w := width) value.1.2) targetWord_get state)

/-- Exact full-frame action on all quantum input labels, including arbitrary flags. -/
lemma rotationGates_step (state : Registers) :
    stepList rotationGates state =
      ((state.1.1, ((BitVec.ofFin (w := width) state.1.2).rotateLeft 1).toFin), state.2) := by
  have retained := rotation_complement state
  have target := rotation_target state
  have source : (stepList rotationGates state).1.1 = state.1.1 :=
    rotation_source _ _ retained
  have flag : (stepList rotationGates state).2 = state.2 := rotation_flag _ _ retained
  have targetFin : (stepList rotationGates state).1.2 =
      ((BitVec.ofFin (w := width) state.1.2).rotateLeft 1).toFin :=
    readout_fin_eq _ _ target
  exact rotation_coordinates_eq source targetFin flag

end

/-- The complete reversed list restores the original physical frame. -/
lemma inverseRotation_rotation (state : Registers) :
    stepList inverseRotationGates (stepList rotationGates state) = state :=
  stepList_reverse_stepList rotationGates state

/-- Full unitary realization retains phases and therefore arbitrary external references. -/
lemma rotation_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding rotationProgram environment
      (fun state =>
        ((state.1.1, ((BitVec.ofFin (w := width) state.1.2).rotateLeft 1).toFin), state.2)) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty rotationGates
    rotationGates_step environment

/-- The actual rotation pays three CNOTs for each of the 255 adjacent swaps. -/
lemma rotation_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      rotationProgram.eventCost = 765 := by
  rw [rotationProgram, programList_cnot_count_eq_sum]
  exact EncodedBit.Word.adjacentShiftLeftGates_cnotMultiplicity_sum
    targetWord targetWord_distinct

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
