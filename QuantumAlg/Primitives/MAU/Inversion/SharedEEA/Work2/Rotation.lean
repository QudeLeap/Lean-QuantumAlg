/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Rotation

/-!
# Actual native circular rotations of the complete second shared word

The optimized EEA step moves the complete Work2 word, including both
payloads and their current boundary, before or after its arithmetic block
[LYL+26, sec_EEA/sub_opt.tex:37-40,68-70]. Each rotation here is the literal
adjacent-swap sweep on the existing Work2 wires, with three CNOT gates per
swap. Its inverse executes the same native list in reverse.

The exact basis action changes only Work2. Every other field and every
possible incoming bit value is retained. No padding bit is assumed clean,
and no additional wire is allocated. Conditional phase selection and the
separate ordered shift-counter updates are subsequent compositions of
these actual operations, rather than assumptions of this leaf.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Work2Rotation

noncomputable section

open EncodedBit

/-- Work2 in physical most-significant-first order, matching its source circular rotation. -/
def word (width : Nat) : Word (encoding width) (width + 3) :=
  ⟨secondWordBit width⟩

private theorem word_distinct (width : Nat) (left right : Fin (width + 3))
    (different : left ≠ right) :
    ((word width).bit left).wire ≠ ((word width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (secondWordBit width left).wire.val = (secondWordBit width right).wire.val at values
  rw [secondWordBit_wire, secondWordBit_wire] at values
  exact different (Fin.ext (by omega))

/-- The actual left sweep contains only the existing adjacent-pair CNOT swaps. -/
def leftGates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.adjacentShiftLeftGates (word width) (word_distinct width)

/-- The actual right sweep is the reversed native left-sweep list. -/
def rightGates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.adjacentShiftRightGates (word width) (word_distinct width)

/-- The left rotation is the circuit compiled from the same literal gate list. -/
def leftProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (leftGates width)

/-- The right rotation is the circuit compiled from the literal inverse gate list. -/
def rightProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (rightGates width)

private def withoutWord {width : Nat} (state : Registers width) : Registers width :=
  { state with secondWord := 0#(width + 3) }

private theorem withoutWord_flip (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    withoutWord ((secondWordBit width index).flip state) = withoutWord state := rfl

private theorem withoutWord_cnot (width : Nat) (left right : Fin (width + 3))
    (state : Registers width) :
    withoutWord (cnotStep (secondWordBit width left) (secondWordBit width right) state) =
      withoutWord state := by
  unfold cnotStep
  split
  · exact withoutWord_flip width right state
  · rfl

private theorem withoutWord_swap (width : Nat) (index : Fin (width + 3 - 1))
    (state : Registers width) :
    withoutWord (GateSpec.stepList
      (Word.adjacentSwapGates (word width) (word_distinct width) index) state) =
        withoutWord state := by
  simp only [Word.adjacentSwapGates, swapGates, GateSpec.stepList, GateSpec.step, word,
    id_eq, withoutWord_cnot]

private theorem withoutWord_indices (width : Nat) (indices : List (Fin (width + 3 - 1)))
    (state : Registers width) :
    withoutWord (GateSpec.stepList
      (indices.flatMap (Word.adjacentSwapGates (word width) (word_distinct width))) state) =
        withoutWord state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, ih, withoutWord_swap]

private theorem left_preserves_complement (width : Nat) (state : Registers width) :
    withoutWord (GateSpec.stepList (leftGates width) state) = withoutWord state :=
  withoutWord_indices width _ state

private theorem left_word (width : Nat) (state : Registers width) :
    (GateSpec.stepList (leftGates width) state).secondWord = state.secondWord.rotateLeft 1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have entry := Word.adjacentShiftLeftStep_get_indexPerm
    (word width) (word_distinct width) ⟨index, within⟩ state
  rw [Word.adjacentSwapIndexPerm_ofFn_eq_finRotate] at entry
  change (secondWordBit width ⟨index, within⟩).get
    (GateSpec.stepList (leftGates width) state) =
      (secondWordBit width (finRotate (width + 3) ⟨index, within⟩)).get state at entry
  rw [secondWordBit_get, secondWordBit_get] at entry
  have position : (finRotate (width + 3) ⟨index, within⟩).val =
      (1 + index) % (width + 3) := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one]
    exact congrArg (fun value => value % (width + 3)) (Nat.add_comm index 1)
  rw [position] at entry
  simpa only [BitVec.getMsbD_rotateLeft, within, decide_true, Bool.true_and] using entry

/-- The actual native left sweep rotates the full word and retains the complete other frame. -/
theorem left_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (leftGates width) state =
      { state with secondWord := state.secondWord.rotateLeft 1 } := by
  let result := GateSpec.stepList (leftGates width) state
  calc
    result = { withoutWord result with secondWord := result.secondWord } := rfl
    _ = _ := by
      rw [left_preserves_complement, left_word]
      rfl

/-- Reversing the actual native list restores every original frame bit. -/
theorem right_left (width : Nat) (state : Registers width) :
    GateSpec.stepList (rightGates width) (GateSpec.stepList (leftGates width) state) = state :=
  Word.adjacentShiftRightStep_adjacentShiftLeftStep (word width) (word_distinct width) state

/-- The actual forward list also reverses the inverse list on every possible incoming frame. -/
theorem left_right (width : Nat) (state : Registers width) :
    GateSpec.stepList (leftGates width) (GateSpec.stepList (rightGates width) state) = state :=
  Word.adjacentShiftLeftStep_adjacentShiftRightStep (word width) (word_distinct width) state

/-- The inverse native sweep rotates right and retains the complete other frame. -/
theorem right_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (rightGates width) state =
      { state with secondWord := state.secondWord.rotateRight 1 } := by
  let result := GateSpec.stepList (rightGates width) state
  have retained : withoutWord result = withoutWord state :=
    (left_preserves_complement width result).symm.trans
      (congrArg withoutWord (left_right width state))
  have rotated := congrArg Registers.secondWord (left_right width state)
  rw [left_step] at rotated
  change result.secondWord.rotateLeft 1 = state.secondWord at rotated
  have inverse := congrArg (fun value : BitVec (width + 3) => value.rotateRight 1) rotated
  rw [NumberTheory.SharedEEA.WordRotation.rotateRight_rotateLeft] at inverse
  calc
    result = { withoutWord result with secondWord := result.secondWord } := rfl
    _ = _ := by
      rw [retained, inverse]
      rfl

/-- Exact full-frame realization by the actual left CNOT circuit, with no phase discarded. -/
theorem left_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (leftProgram width)
      (fun state => { state with secondWord := state.secondWord.rotateLeft 1 }) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (leftGates width) (left_step width)

/-- Exact full-frame realization by the actual inverse CNOT circuit. -/
theorem right_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (rightProgram width)
      (fun state => { state with secondWord := state.secondWord.rotateRight 1 }) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (rightGates width) (right_step width)

/-- The actual left event trace has three native CNOT events per adjacent Work2 pair. -/
theorem left_eventTrace_length (width : Nat) :
    (leftProgram width).eventTrace.length = 3 * (width + 2) := by
  rw [leftProgram, GateSpec.programList_eventTrace, List.length_map]
  exact (Word.adjacentShiftLeftGates_length (word width) (word_distinct width)).trans
    (congrArg (3 * ·) (by omega))

/-- The literal inverse list has the same exact number of native events. -/
theorem right_eventTrace_length (width : Nat) :
    (rightProgram width).eventTrace.length = 3 * (width + 2) := by
  rw [rightProgram, GateSpec.programList_eventTrace, List.length_map]
  exact (Word.adjacentShiftRightGates_length (word width) (word_distinct width)).trans
    (congrArg (3 * ·) (by omega))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Work2Rotation
