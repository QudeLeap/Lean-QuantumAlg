/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Control.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Increment
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Work2.PhaseRotation

/-!
# Actual Ctrl-controlled Work2 and complete existing-wire clock operations

Each pair first rotates the existing Work2 and then updates the existing
complete shift counter, matching the ordered assignments in the optimized
source [LYL+26, sec_EEA/sub_opt.tex:37-40,68-70]. The word operations are
the actual Toffoli sweeps. The finite increment is the actual HRS circuit
with its entire borrowed Work2 restored, and decrement is its literal
dagger [HRS16, paper.tex:219-224].

All control placement uses the same explicit exchange of logical and
physical wire names. The two high bits are original Work1 positions. The arbitrary incoming Ctrl
is preserved; a later
source-phase computation determines its active value. No input promise,
extra register, or replacement execution mechanism is introduced here.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlledShift

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def wordStep {width : Nat} (action : BitVec (width + 3) → BitVec (width + 3))
    (state : Registers width) : Registers width :=
  if state.control then { state with secondWord := action state.secondWord } else state

private def counterStep {width : Nat}
    (action : BitVec (width + 3) × BitVec width.size →
      BitVec (width + 3) × BitVec width.size)
    (state : Registers width) : Registers width :=
  if state.control then
    let pair := action (state.firstWord, state.shift)
    { state with firstWord := pair.1, shift := pair.2 }
  else state

private theorem exchanged_word (width : Nat) (action : BitVec (width + 3) → BitVec (width + 3))
    (state : Registers width) :
    ControlPlacement.placedStep
      (fun state => if state.flags.second then
        { state with secondWord := action state.secondWord } else state) state =
      wordStep action state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases control <;> rfl

private theorem exchanged_counter (width : Nat)
    (action : BitVec (width + 3) × BitVec width.size →
      BitVec (width + 3) × BitVec width.size) (state : Registers width) :
    ControlPlacement.placedStep
      (fun state => if state.flags.second then
        let pair := action (state.firstWord, state.shift)
        { state with firstWord := pair.1, shift := pair.2 } else state) state =
      counterStep action state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases control <;> rfl

/-- The actual left Toffoli sweep, controlled by the existing Ctrl instead of Phase2. -/
def leftWordProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  ControlPlacement.place width (GateSpec.programList (Work2PhaseRotation.leftGates width))

/-- The actual right Toffoli sweep with the same physical Ctrl placement. -/
def rightWordProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  ControlPlacement.place width (GateSpec.programList (Work2PhaseRotation.rightGates width))

/-- The actual HRS incrementer on the existing source fields, controlled by Ctrl. -/
def incrementProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  ControlPlacement.place width (ExtendedClockIncrement.program width)

private theorem leftWord_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (leftWordProgram width)
      (wordStep (fun word => word.rotateLeft 1)) :=
  (ControlPlacement.place_realizes width
    (GateSpec.realizesList_congrStep (Work2PhaseRotation.leftGates width)
      (Work2PhaseRotation.left_step width))).congrStep (by
        intro state
        exact exchanged_word width (fun word => word.rotateLeft 1) state)

private theorem rightWord_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (rightWordProgram width)
      (wordStep (fun word => word.rotateRight 1)) :=
  (ControlPlacement.place_realizes width
    (GateSpec.realizesList_congrStep (Work2PhaseRotation.rightGates width)
      (Work2PhaseRotation.right_step width))).congrStep (by
        intro state
        exact exchanged_word width (fun word => word.rotateRight 1) state)

private theorem increment_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (incrementProgram width)
      (counterStep PaddingClock.increment) :=
  (ControlPlacement.place_realizes width (ExtendedClockIncrement.program_realizes width)).congrStep
    (by
      intro state
      exact exchanged_counter width PaddingClock.increment state)

private theorem decrement_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (incrementProgram width).dagger
      (counterStep PaddingClock.decrement) := by
  apply (increment_realizes width).dagger_of_rightInverse
  intro state
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases control with
  | false => rfl
  | true =>
      simp only [counterStep, if_true]
      exact congrArg
        (fun pair : BitVec (width + 3) × BitVec width.size =>
          Registers.mk pair.1 word2 lengthT lengthQ lengthR pair.2 ⟨p1, p2, sign, iter⟩ true)
        (PaddingClock.increment_decrement (word1, shift))

/-- One actual left rotation is followed by the actual finite increment. -/
def leftProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (leftWordProgram width).seq (incrementProgram width)

/-- One actual right rotation is followed by the actual finite decrement. -/
def rightProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (rightWordProgram width).seq (incrementProgram width).dagger

/-- Retain all fields while applying the ordered left-word/increment assignment on Ctrl. -/
def leftStep {width : Nat} (state : Registers width) : Registers width :=
  if state.control then
    let pair := PaddingClock.increment (state.firstWord, state.shift)
    { state with firstWord := pair.1, secondWord := state.secondWord.rotateLeft 1, shift := pair.2 }
  else state

/-- Retain all fields while applying the ordered right-word/decrement assignment on Ctrl. -/
def rightStep {width : Nat} (state : Registers width) : Registers width :=
  if state.control then
    let pair := PaddingClock.decrement (state.firstWord, state.shift)
    { state with
      firstWord := pair.1
      secondWord := state.secondWord.rotateRight 1
      shift := pair.2 }
  else state

/-- Exact ordered left-pair action includes the complete clock and restored Work2. -/
theorem left_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (leftProgram width) leftStep :=
  ((leftWord_realizes width).seq (increment_realizes width)).congrStep (by
    intro state
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iter⟩, control⟩
    cases control <;> rfl)

/-- Exact full-register realization of the actual ordered right pair. -/
theorem right_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (rightProgram width) rightStep :=
  ((rightWord_realizes width).seq (decrement_realizes width)).congrStep (by
    intro state
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iter⟩, control⟩
    cases control <;> rfl)

/-- The actual left trace retains both the Toffoli sweep and every native HRS event in order. -/
theorem left_eventTrace (width : Nat) :
    (leftProgram width).eventTrace =
      (Work2PhaseRotation.leftGates width).map GateSpec.event ++
        (ExtendedClockIncrement.program width).eventTrace := by
  rw [leftProgram, UnitaryCircuit.seq_eventTrace, leftWordProgram,
    ControlPlacement.place_eventTrace, GateSpec.programList_eventTrace,
    incrementProgram, ControlPlacement.place_eventTrace]

/-- The actual right trace retains the word sweep followed by the reversed finite-counter trace. -/
theorem right_eventTrace (width : Nat) :
    (rightProgram width).eventTrace =
      (Work2PhaseRotation.rightGates width).map GateSpec.event ++
        (ExtendedClockIncrement.program width).eventTrace.reverse := by
  rw [rightProgram, UnitaryCircuit.seq_eventTrace, rightWordProgram,
    ControlPlacement.place_eventTrace, GateSpec.programList_eventTrace,
    UnitaryCircuit.dagger_eventTrace, incrementProgram, ControlPlacement.place_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlledShift
