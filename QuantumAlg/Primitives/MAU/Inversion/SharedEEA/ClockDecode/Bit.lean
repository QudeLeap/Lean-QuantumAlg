/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Work2.Rotation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Predicate.Layout
import all QuantumAlg.Components.Encoded.BitGates.Controlled.SwapLaws
import all QuantumAlg.Components.Encoded.BitGates.ConditionalListLaws

/-!
# Actual Work2 inverse rotation under one retained complete-clock bit

The terminal repair retains the displacement in the original low shift
field and two original Work1 positions. Decoding rotates the entire Work2
right while retaining that history for subsequent inverse computation
[LYL+26, sec_EEA/sub_4phase.tex:105,121-128]. This is an internal corrective
gate construction, not a claim that the paper already emits this decoder.

Every adjacent controlled swap is the existing three-Toffoli list. Its
control is a real retained clock wire, disjoint from every Work2 wire.
The complete input frame is allowed; no clock-bit value or dirty-work
initialization is assumed, and no additional work wire is used.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ClockDecodeBit

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit PredicateLayout

private lemma separate (width : Nat) (clock : Fin (width.size + 2))
    (index : Fin (width + 3)) :
    (clockBit width clock).wire ≠ ((Work2Rotation.word width).bit index).wire := by
  intro same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  change (clockBit width clock).wire.val = (secondWordBit width index).wire.val at values
  rw [TerminalPredicateLayout.clockBit_wire, secondWordBit_wire] at values
  have clockBound := clock.isLt
  have wordBound := index.isLt
  split_ifs at values <;> omega

/-- Every selecting bit reads its actual original high or low clock coordinate. -/
lemma control_get (width : Nat) (clock : Fin (width.size + 2)) (state : Registers width) :
    (clockBit width clock).get state =
      if clock.val < 2 then
        (NumberTheory.SharedEEA.PaddingClock.high state.firstWord).getMsbD clock.val
      else state.shift.getMsbD (clock.val - 2) :=
  extendedClock_source_get width clock state

private lemma control_setWord (width : Nat) (clock : Fin (width.size + 2))
    (word : BitVec (width + 3)) (state : Registers width) :
    (clockBit width clock).get { state with secondWord := word } =
      (clockBit width clock).get state := by
  simp only [control_get]

private def leftGates (width : Nat) (clock : Fin (width.size + 2)) :
    List (GateSpec (encoding width)) :=
  Word.controlledAdjacentShiftLeftGates (clockBit width clock) (Work2Rotation.word width)
    (separate width clock) (Work2Rotation.word_distinct width)

/-- The actual inverse sweep contains exactly the reversed three-Toffoli adjacent swaps. -/
def gates (width : Nat) (clock : Fin (width.size + 2)) : List (GateSpec (encoding width)) :=
  (leftGates width clock).reverse

private lemma left_conditional (width : Nat) (clock : Fin (width.size + 2))
    (state : Registers width) :
    GateSpec.stepList (leftGates width clock) state =
      if (clockBit width clock).get state then GateSpec.stepList (Work2Rotation.leftGates width)
        state else state := by
  refine GateSpec.stepList_flatMap_if
    (fun state : Registers width => (clockBit width clock).get state = true)
    (Word.adjacentSwapGates (Work2Rotation.word width) (Work2Rotation.word_distinct width))
    (Word.controlledAdjacentSwapGates (clockBit width clock) (Work2Rotation.word width)
      (separate width clock) (Work2Rotation.word_distinct width)) ?_ ?_
    (List.ofFn fun index : Fin (width + 3 - 1) => index) state
  · intro index current
    exact controlledSwapStep_eq_if (clockBit width clock)
      ((Work2Rotation.word width).bit (Word.adjacentLeftIndex (width + 3) index))
      ((Work2Rotation.word width).bit (Word.adjacentRightIndex (width + 3) index))
      (separate width clock _) (separate width clock _) (Work2Rotation.word_distinct width _ _
        (Word.adjacentLeftIndex_ne_adjacentRightIndex (width + 3) index)) current
  · intro index current
    have retained : (clockBit width clock).get (GateSpec.stepList
        (Word.adjacentSwapGates (Work2Rotation.word width)
          (Work2Rotation.word_distinct width) index) current) =
        (clockBit width clock).get current :=
      swapStep_get_observed_of_swap_ne _ _ _ _
        (separate width clock _).symm (separate width clock _).symm current
    change (_ = true) ↔ (_ = true)
    rw [retained]

/-- The literal decoder gate list rotates right only on the actual selected clock value. -/
lemma gates_step (width : Nat) (clock : Fin (width.size + 2)) (state : Registers width) :
    GateSpec.stepList (gates width clock) state =
      if (clockBit width clock).get state then
        { state with secondWord := state.secondWord.rotateRight 1 } else state := by
  let previous := if (clockBit width clock).get state then
    GateSpec.stepList (Work2Rotation.rightGates width) state else state
  have forward : GateSpec.stepList (leftGates width clock) previous = state := by
    by_cases selected : (clockBit width clock).get state = true
    · dsimp only [previous]
      rw [if_pos selected, left_conditional]
      have retained :
          (clockBit width clock).get (GateSpec.stepList (Work2Rotation.rightGates width) state) =
            (clockBit width clock).get state := by
        rw [Work2Rotation.right_step]
        exact control_setWord width clock _ state
      rw [retained, if_pos selected, Work2Rotation.left_right]
    · dsimp only [previous]
      rw [if_neg selected, left_conditional, if_neg selected]
  calc
    _ = GateSpec.stepList (gates width clock)
        (GateSpec.stepList (leftGates width clock) previous) :=
      congrArg (GateSpec.stepList (gates width clock)) forward.symm
    _ = previous := GateSpec.stepList_reverse_stepList (leftGates width clock) previous
    _ = _ := by
      dsimp only [previous]
      rw [Work2Rotation.right_step]

/-- Every selecting clock bit, including both high positions, is retained exactly. -/
lemma gates_clockBit (width : Nat) (clock observed : Fin (width.size + 2))
    (state : Registers width) :
    (clockBit width observed).get (GateSpec.stepList (gates width clock) state) =
      (clockBit width observed).get state := by
  rw [gates_step]
  split
  · exact control_setWord width observed _ state
  · rfl

/-- Compile precisely the same actual adjacent-Toffoli decoder sweep. -/
def program (width : Nat) (clock : Fin (width.size + 2)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width clock)

/-- Exact complete-frame basis semantics retains all relative amplitudes and history values. -/
lemma program_realizes (width : Nat) (clock : Fin (width.size + 2)) :
    UnitaryCircuit.Realizes (encoding width) (program width clock) environment
      (fun state => if (clockBit width clock).get state then
        { state with secondWord := state.secondWord.rotateRight 1 } else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width clock) environment

/-- The actual trace contains every emitted adjacent-swap Toffoli on every input. -/
lemma program_eventTrace (width : Nat) (clock : Fin (width.size + 2)) :
    (program width clock).eventTrace = (gates width clock).map (GateSpec.event .empty) :=
  GateSpec.programList_eventTrace (QubitLayout.canonical _) .empty _

/-- The physical one-bit-controlled inverse sweep has exactly three gates per adjacent pair. -/
lemma gates_length (width : Nat) (clock : Fin (width.size + 2)) :
    (gates width clock).length = 3 * (width + 2) := by
  rw [gates, List.length_reverse, leftGates, Word.controlledAdjacentShiftLeftGates_length]
  omega

/-- The literal one-bit-controlled decoder sweep has this exact strict unit depth. -/
lemma program_unitDepth (width : Nat) (clock : Fin (width.size + 2)) :
    (program width clock).evaluatedEventDepth (fun _ => 1) = 3 * (width + 2) := by
  rw [program, GateSpec.programList_evaluatedEventDepth_unit, gates_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ClockDecodeBit
