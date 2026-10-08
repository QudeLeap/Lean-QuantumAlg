/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Work2.Rotation
import all QuantumAlg.Components.Encoded.BitGates.Controlled.SwapLaws

/-!
# Actual phase-controlled Work2 rotations

The optimized source orders one left rotation before two right rotations
controlled by the retained Phase2 wire [LYL+26, sec_EEA/sub_opt.tex:37-40,68-70].
The controlled sweeps here use three actual Toffoli gates per adjacent pair.
Their full-frame action is the corresponding conditional CNOT sweep, with
the control and all other fields preserved exactly.

The final composition retains the literal left/right/right gate order. It
implements the word part of that source operation. The outer Phase1 guard
and the interleaved finite-counter updates remain separate integration
obligations. No native selector, workspace, or clean-control promise is
introduced by this module.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Work2PhaseRotation

noncomputable section

open EncodedBit

private theorem separate (width : Nat) (index : Fin (width + 3)) :
    (phase2Bit width).wire ≠ ((Work2Rotation.word width).bit index).wire := by
  intro same
  have values := congrArg Fin.val same
  change (phase2Bit width).wire.val = (secondWordBit width index).wire.val at values
  rw [phase2Bit_wire, secondWordBit_wire] at values
  have bounded := index.isLt
  omega

/-- The existing Phase2 wire controls an actual left sweep of Toffoli gates. -/
def leftGates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.controlledAdjacentShiftLeftGates (phase2Bit width) (Work2Rotation.word width)
    (separate width) (Work2Rotation.word_distinct width)

/-- The same controlled sweep in reverse is the actual right-rotation gate list. -/
def rightGates (width : Nat) : List (GateSpec (encoding width)) :=
  (leftGates width).reverse

private theorem swap_control (width : Nat) (index : Fin (width + 3 - 1))
    (state : Registers width) :
    (phase2Bit width).get (GateSpec.stepList
      (Word.adjacentSwapGates (Work2Rotation.word width)
        (Work2Rotation.word_distinct width) index) state) = (phase2Bit width).get state :=
  swapStep_get_observed_of_swap_ne _ _ _ _
    (separate width _).symm (separate width _).symm state

private theorem indices_step (width : Nat) (indices : List (Fin (width + 3 - 1)))
    (state : Registers width) :
    GateSpec.stepList (indices.flatMap
      (Word.controlledAdjacentSwapGates (phase2Bit width) (Work2Rotation.word width)
        (separate width) (Work2Rotation.word_distinct width))) state =
      if (phase2Bit width).get state then
        GateSpec.stepList (indices.flatMap (Word.adjacentSwapGates (Work2Rotation.word width)
          (Work2Rotation.word_distinct width))) state else state := by
  induction indices generalizing state with
  | nil => simp [GateSpec.stepList]
  | cons index rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append]
      have selected := controlledSwapStep_eq_if (phase2Bit width)
        ((Work2Rotation.word width).bit (Word.adjacentLeftIndex (width + 3) index))
        ((Work2Rotation.word width).bit (Word.adjacentRightIndex (width + 3) index))
        (separate width _) (separate width _) (Work2Rotation.word_distinct width _ _
          (Word.adjacentLeftIndex_ne_adjacentRightIndex (width + 3) index)) state
      change GateSpec.stepList
        (Word.controlledAdjacentSwapGates (phase2Bit width) (Work2Rotation.word width)
          (separate width) (Work2Rotation.word_distinct width) index) state =
        if (phase2Bit width).get state then
          GateSpec.stepList (Word.adjacentSwapGates (Work2Rotation.word width)
            (Work2Rotation.word_distinct width) index) state else state at selected
      rw [selected]
      by_cases chosen : (phase2Bit width).get state
      · rw [if_pos chosen, ih, swap_control, if_pos chosen, if_pos chosen,
          List.flatMap_cons, GateSpec.stepList_append]
      · rw [if_neg chosen, ih, if_neg chosen, if_neg chosen]

private theorem left_conditional (width : Nat) (state : Registers width) :
    GateSpec.stepList (leftGates width) state =
      if state.flags.second then GateSpec.stepList (Work2Rotation.leftGates width) state
      else state :=
  indices_step width _ state

/-- The controlled native left sweep has the complete conditional frame update. -/
theorem left_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (leftGates width) state =
      if state.flags.second then { state with secondWord := state.secondWord.rotateLeft 1 }
      else state := by
  rw [left_conditional, Work2Rotation.left_step]

/-- The inverse native list conditionally rotates right and restores every other field. -/
theorem right_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (rightGates width) state =
      if state.flags.second then { state with secondWord := state.secondWord.rotateRight 1 }
      else state := by
  let candidate := if state.flags.second then
    GateSpec.stepList (Work2Rotation.rightGates width) state else state
  have forward : GateSpec.stepList (leftGates width) candidate = state := by
    by_cases chosen : state.flags.second
    · dsimp only [candidate]
      rw [if_pos chosen, left_conditional]
      have retained : (GateSpec.stepList (Work2Rotation.rightGates width) state).flags.second =
          state.flags.second := by
        rw [Work2Rotation.right_step]
      rw [retained, if_pos chosen, Work2Rotation.left_right]
    · dsimp only [candidate]
      rw [if_neg chosen, left_conditional, if_neg chosen]
  calc
    GateSpec.stepList (rightGates width) state =
        GateSpec.stepList (rightGates width) (GateSpec.stepList (leftGates width) candidate) :=
      congrArg (GateSpec.stepList (rightGates width)) forward.symm
    _ = candidate := GateSpec.stepList_reverse_stepList (leftGates width) candidate
    _ = _ := by
      dsimp only [candidate]
      rw [Work2Rotation.right_step]

/-- The literal source word sequence keeps both selected inverse sweeps after the left sweep. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  Work2Rotation.leftGates width ++ rightGates width ++ rightGates width

/-- Complete action of the actual ordered word operations, before adding the counter operations. -/
theorem gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state =
      { state with secondWord :=
        if state.flags.second then
          ((state.secondWord.rotateLeft 1).rotateRight 1).rotateRight 1
        else state.secondWord.rotateLeft 1 } := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append, Work2Rotation.left_step,
    right_step]
  cases chosen : state.flags.second <;> simp only [chosen, Bool.false_eq_true, if_false,
    if_true, right_step]

/-- Compile exactly the ordered CNOT and phase-controlled Toffoli lists. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

/-- The actual program has the full conditional frame action with exact amplitudes. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width)
      (fun state => { state with secondWord :=
        if state.flags.second then
          ((state.secondWord.rotateLeft 1).rotateRight 1).rotateRight 1
        else state.secondWord.rotateLeft 1 }) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width) (gates_step width)

/-- All three sweeps remain in the actual trace, including on the unselected basis subspace. -/
theorem program_eventTrace_length (width : Nat) :
    (program width).eventTrace.length = 9 * (width + 2) := by
  have left := Word.adjacentShiftLeftGates_length
    (Work2Rotation.word width) (Work2Rotation.word_distinct width)
  have selected := Word.controlledAdjacentShiftLeftGates_length
    (phase2Bit width) (Work2Rotation.word width) (separate width)
      (Work2Rotation.word_distinct width)
  change (Work2Rotation.leftGates width).length = 3 * (width + 3 - 1) at left
  change (leftGates width).length = 3 * (width + 3 - 1) at selected
  rw [program, GateSpec.programList_eventTrace, List.length_map, gates, List.length_append,
    List.length_append, rightGates, List.length_reverse, left, selected]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Work2PhaseRotation
