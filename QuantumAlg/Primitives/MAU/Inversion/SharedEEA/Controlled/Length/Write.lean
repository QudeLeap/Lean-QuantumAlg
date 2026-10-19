/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Length.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Schedule
import all QuantumAlg.Components.Encoded.BitGates.ConditionalListLaws

/-!
# Actual length-write enumerations selected by retained Ctrl

The actual set-bit, leading-position, and boundary-key enumerations are
those of the original native length writer. Every candidate adds original
Ctrl as one positive source of its actual pattern, retaining the same
arbitrary Iter work. The existing finite-list refinement law transports
the original complete length semantics through these real replacements
[LYL+26, sec_EEA/sub_regshare.tex:310-314;
LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341].

The selecting Ctrl remains unchanged while either length output changes.
No precomputed length or boundary condition is supplied to the circuit.
The complete action includes all false-control inputs and empty regions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthWrite

noncomputable section

open EncodedBit LengthCoordinates

private lemma constant_control (width : Nat) (field : Field) (constant : Fin (2 ^ width.size))
    (state : Registers width) :
    (Word.xorConstantStep (LengthWrite.target width field) constant state).control =
      state.control := by
  rw [LengthField.constant_step_eq]
  cases field <;> rfl

/-- Every set bit of the actual fixed length label emits the actual controlled candidate. -/
def positionGates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) : List (GateSpec (encoding width)) :=
  (Word.constantOneIndices (LengthWrite.positionConstant width field key position)).flatMap
    (ControlledLengthPredicate.gates width field key firstWord position)

/-- Full actual constant-write refinement retains Ctrl and the entire original register action. -/
lemma position_step_if (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (state : Registers width) :
    GateSpec.stepList (positionGates width field key firstWord position) state =
      if state.control
      then GateSpec.stepList (LengthWrite.positionGates width field key firstWord position) state
      else state :=
  GateSpec.stepList_flatMap_if (fun state : Registers width => state.control = true)
    (LengthPredicate.gates width field key firstWord position)
    (ControlledLengthPredicate.gates width field key firstWord position)
    (ControlledLengthPredicate.gates_step_if width field key firstWord position)
    (fun output state => by
      rw [ControlledLengthPredicate.original_control width field key firstWord position output])
    _ state

private lemma original_position_control (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (state : Registers width) :
    (GateSpec.stepList (LengthWrite.positionGates width field key firstWord position)
      state).control = state.control := by
  rw [LengthWrite.positionGates_step]
  split
  · exact constant_control width field _ state
  · rfl

/-- All leading positions retain their literal order and their true controlled native lists. -/
def keyGates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool) :
    List (GateSpec (encoding width)) :=
  (List.ofFn fun position : Fin (region width field key) => position).flatMap
    (positionGates width field key firstWord)

/-- The actual fixed-key read is exactly the original complete native read under retained Ctrl. -/
lemma key_step_if (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (state : Registers width) :
    GateSpec.stepList (keyGates width field key firstWord) state =
      if state.control then GateSpec.stepList (LengthWrite.gates width field key firstWord) state
      else state :=
  GateSpec.stepList_flatMap_if (fun state : Registers width => state.control = true)
    (LengthWrite.positionGates width field key firstWord)
    (positionGates width field key firstWord)
    (position_step_if width field key firstWord)
    (fun position state => by
      rw [original_position_control width field key firstWord position]) _ state

private lemma original_key_control (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (state : Registers width) :
    (GateSpec.stepList (LengthWrite.gates width field key firstWord) state).control =
      state.control := by
  rw [LengthWrite.gates_step]
  split
  · exact constant_control width field _ state
  · rfl

/-- Every possible retained boundary key is included, independently of the quantum input. -/
def gates (width : Nat) (field : Field) (firstWord : Bool) : List (GateSpec (encoding width)) :=
  (LengthSchedule.keys width).flatMap fun key => keyGates width field key firstWord

/-- The full emitted sequence conditionally performs the entire original dynamic length write. -/
lemma gates_step_if (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    GateSpec.stepList (gates width field firstWord) state =
      if state.control then GateSpec.stepList (LengthSchedule.gates width field firstWord) state
      else state :=
  GateSpec.stepList_flatMap_if (fun state : Registers width => state.control = true)
    (fun key => LengthWrite.gates width field key firstWord)
    (fun key => keyGates width field key firstWord)
    (fun key => key_step_if width field key firstWord)
    (fun key state => by rw [original_key_control width field key firstWord]) _ state

/-- Its exact result is the existing independent finite length XOR on every full frame. -/
lemma gates_step (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    GateSpec.stepList (gates width field firstWord) state =
      if state.control then LengthSchedule.step width field firstWord state else state := by
  rw [gates_step_if, LengthSchedule.gates_step]

/-- The complete original dynamic writer retains Ctrl while updating its true output field. -/
lemma original_control (width : Nat) (field : Field) (firstWord : Bool)
    (state : Registers width) :
    (GateSpec.stepList (LengthSchedule.gates width field firstWord) state).control =
      state.control := by
  rw [LengthSchedule.gates_step]
  cases field <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthWrite
