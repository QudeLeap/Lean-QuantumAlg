/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Guard
import all QuantumAlg.Util.NumberTheory.SharedEEA.PaddingClock.Active

/-!
# Actual guarded source shifts with predicate cleanup

The pre-shift and post-shift blocks use the same actual sequence:
compute the selected Phase1 predicate, rotate left, increment the complete
existing-wire clock, and reverse the predicate. Then compute the joint descending
predicate, perform two ordered right-rotation/decrement pairs, and reverse
that predicate [LYL+26, sec_EEA/sub_opt.tex:37-40,68-70]. The intermediate
increment and both finite decrements remain actual executed operations.

The full-register realization allows every incoming Ctrl value and restores
it exactly. Only the source-specialization lemma uses the Ctrl-zero invariant
established by the algorithm's own preparation. It is not a new condition on
the original mathematical input. The complete clock uses two original Work1 positions;
active no-carry and no-borrow facts come from the actual phase trajectory.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedShift

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit NumberTheory.SharedEEA

private def ascending {width : Nat} (state : Registers width) : Registers width :=
  let pair := PaddingClock.increment (state.firstWord, state.shift)
  { state with
    firstWord := pair.1
    secondWord := state.secondWord.rotateLeft 1
    shift := pair.2 }

private def descending {width : Nat} (state : Registers width) : Registers width :=
  let pair := PaddingClock.decrement (PaddingClock.decrement (state.firstWord, state.shift))
  { state with
    firstWord := pair.1
    secondWord := (state.secondWord.rotateRight 1).rotateRight 1
    shift := pair.2 }

/-- A reached ascending bound restores arbitrary original high positions internally. -/
lemma ascending_eq_low {width : Nat} (state : Registers width)
    (within : state.shift.toNat + 1 < 2 ^ width.size) :
    ascending state =
      { state with secondWord := state.secondWord.rotateLeft 1, shift := state.shift + 1 } := by
  unfold ascending
  rw [PaddingClockActive.increment_eq_low (state.firstWord, state.shift) within]

/-- The actual intermediate increment and two inverse increments retain arbitrary high data. -/
lemma descending_ascending_eq_low {width : Nat} (state : Registers width)
    (positive : 0 < state.shift.toNat) :
    descending (ascending state) =
      { state with
        secondWord := ((state.secondWord.rotateLeft 1).rotateRight 1).rotateRight 1
        shift := state.shift - 1 } := by
  unfold descending ascending
  rw [PaddingClockActive.descending_eq_low (state.firstWord, state.shift) positive]

private def firstStep {width : Nat} (selected : Bool) (state : Registers width) : Registers width :=
  if state.control ^^ PhaseGuard.firstPredicate selected state then ascending state else state

private def lastStep {width : Nat} (selected : Bool) (state : Registers width) : Registers width :=
  if state.control ^^ PhaseGuard.descendingPredicate selected state then descending state else state

private def firstProgram (width : Nat) (selected : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (GateSpec.programList (QubitLayout.canonical _) .empty
    (PhaseGuard.firstGates width selected)).seq
    ((ControlledShift.leftProgram width).seq
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (PhaseGuard.firstGates width selected).reverse))

private def lastProgram (width : Nat) (selected : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (GateSpec.programList (QubitLayout.canonical _) .empty
    (PhaseGuard.descendingGates width selected)).seq
    (((ControlledShift.rightProgram width).seq (ControlledShift.rightProgram width)).seq
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (PhaseGuard.descendingGates width selected).reverse))

private lemma first_realizes (width : Nat) (selected : Bool) :
    UnitaryCircuit.Realizes (encoding width) (firstProgram width selected) environment (firstStep
      selected) :=
  ((PhaseGuard.first_realizes width selected).seq
    ((ControlledShift.left_realizes width).seq
      (GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
        (PhaseGuard.firstGates width selected).reverse
        (PhaseGuard.first_reverse_step width selected) environment))).congrStep (by
    intro state
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iter⟩, control⟩
    cases selected <;> cases p1 <;> cases control <;> rfl)

private lemma last_realizes (width : Nat) (selected : Bool) :
    UnitaryCircuit.Realizes (encoding width) (lastProgram width selected) environment (lastStep
      selected) :=
  ((PhaseGuard.descending_realizes width selected).seq
    (((ControlledShift.right_realizes width).seq (ControlledShift.right_realizes width)).seq
      (GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
        (PhaseGuard.descendingGates width selected).reverse
        (PhaseGuard.descending_reverse_step width selected) environment))).congrStep (by
    intro state
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iter⟩, control⟩
    cases selected <;> cases p1 <;> cases p2 <;> cases control <;> rfl)

/-- Execute both source shift stages and their actual inverse predicate cleanup. -/
def program (width : Nat) (selected : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (firstProgram width selected).seq (lastProgram width selected)

/-- Complete actual state action, including arbitrary incoming Ctrl and finite-counter wrap. -/
def step {width : Nat} (selected : Bool) (state : Registers width) : Registers width :=
  lastStep selected (firstStep selected state)

/-- The exact full-frame realization is derived solely from the executed native components. -/
lemma program_realizes (width : Nat) (selected : Bool) :
    UnitaryCircuit.Realizes (encoding width) (program width selected) environment (step selected) :=
  (first_realizes width selected).seq (last_realizes width selected)

private lemma first_control (width : Nat) (selected : Bool) (state : Registers width) :
    (firstStep selected state).control = state.control := by
  unfold firstStep
  split <;> rfl

private lemma last_control (width : Nat) (selected : Bool) (state : Registers width) :
    (lastStep selected state).control = state.control := by
  unfold lastStep
  split <;> rfl

/-- Both actual predicate cleanup stages restore the original Ctrl for every incoming value. -/
lemma step_control (width : Nat) (selected : Bool) (state : Registers width) :
    (step selected state).control = state.control := by
  rw [step, last_control, first_control]

/-- The source shift block, with both right rotations and finite decrements kept explicit. -/
def sourceStep {width : Nat} (selected : Bool) (state : Registers width) : Registers width :=
  if state.flags.first = selected then
    if state.flags.second then descending (ascending state) else ascending state
  else state

/-- The source behavior follows from the algorithm's internal Ctrl-zero invariant. -/
lemma step_eq_source (width : Nat) (selected : Bool) (state : Registers width)
    (preparedControl : state.control = false) :
    step selected state = sourceStep selected state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  change control = false at preparedControl
  subst control
  cases selected <;> cases p1 <;> cases p2 <;> rfl

/-- The actual circuit acts on every internally prepared source label without losing a phase. -/
lemma program_prepared (width : Nat) (selected : Bool) (state : Registers width)
    (preparedControl : state.control = false) :
    (program width selected).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
            ((encoding width).encode state))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
          ((encoding width).encode (sourceStep selected state))) := by
  have actual := (program_realizes
    (environment := environment) width selected).apply_encoded_ket state
  rw [step_eq_source width selected state preparedControl] at actual
  exact actual

/-- The literal event trace retains every predicate, arithmetic pair, and inverse cleanup. -/
lemma program_eventTrace (width : Nat) (selected : Bool) :
    (program width selected).eventTrace =
      (PhaseGuard.firstGates width selected).map (GateSpec.event .empty) ++
      (ControlledShift.leftProgram width).eventTrace ++
      (PhaseGuard.firstGates width selected).reverse.map (GateSpec.event .empty) ++
      (PhaseGuard.descendingGates width selected).map (GateSpec.event .empty) ++
      (ControlledShift.rightProgram width).eventTrace ++
      (ControlledShift.rightProgram width).eventTrace ++
      (PhaseGuard.descendingGates width selected).reverse.map (GateSpec.event .empty) := by
  simp only [program, firstProgram, lastProgram, UnitaryCircuit.seq_eventTrace,
    GateSpec.programList_eventTrace, List.append_assoc]

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedShift
