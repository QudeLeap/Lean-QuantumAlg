/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Length.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Schedule
import all QuantumAlg.Components.Encoded.BitGates.ConditionalListLaws

/-!
# Complete actual guarded finite length-write schedules

The set-bit, leading-position, and retained-key enumerations are the same
as in the original native length writer. Every elementary predicate is
replaced by the actual enlarged-prefix predicate. Complete block and list
refinement therefore proves the guarded action without duplicating the
arithmetic leading-length argument
[LYL+26, sec_EEA/sub_regshare.tex:309-313;
sec_circuit/sub_block_new.tex:211-219,338-341].

Both original quotient and low-shift fields are retained at every layer.
All guard controls are physical source bits in the actual emitted lists.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthWrite

noncomputable section

open EncodedBit LengthCoordinates GuardedLengthRead

private theorem constant_guard (width : Nat) (field : Field) (constant : Fin (2 ^ width.size))
    (state : Registers width) :
    Guard (Word.xorConstantStep (LengthWrite.target width field) constant state) ↔ Guard state := by
  rw [LengthField.constant_step_eq]
  cases field <;> rfl

/-- Each set bit of the original static finite label uses the actual enlarged native predicate. -/
def positionGates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) : List (GateSpec (encoding width)) :=
  (Word.constantOneIndices (LengthWrite.positionConstant width field key position)).flatMap
    (GuardedLengthPredicate.gates width field key firstWord position)

/-- The complete actual replacement of a constant write is its retained-guard conditional action. -/
theorem position_step_if (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (state : Registers width) :
    GateSpec.stepList (positionGates width field key firstWord position) state =
      if Guard state
      then GateSpec.stepList (LengthWrite.positionGates width field key firstWord position) state
      else state :=
  GateSpec.stepList_flatMap_if Guard
    (LengthPredicate.gates width field key firstWord position)
    (GuardedLengthPredicate.gates width field key firstWord position)
    (GuardedLengthPredicate.gates_step_if width field key firstWord position)
    (GuardedLengthPredicate.original_guard width field key firstWord position) _ state

private theorem original_position_guard (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (state : Registers width) :
    Guard (GateSpec.stepList (LengthWrite.positionGates width field key firstWord position) state) ↔
      Guard state := by
  rw [LengthWrite.positionGates_step]
  split
  · exact constant_guard width field _ state
  · rfl

/-- The complete actual leading-position enumeration at one fixed retained key. -/
def keyGates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool) :
    List (GateSpec (encoding width)) :=
  (List.ofFn fun position : Fin (region width field key) => position).flatMap
    (positionGates width field key firstWord)

/-- Refinement of actual complete lists retains the original finite length-write semantics. -/
theorem key_step_if (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (state : Registers width) :
    GateSpec.stepList (keyGates width field key firstWord) state =
      if Guard state then GateSpec.stepList (LengthWrite.gates width field key firstWord) state
      else state :=
  GateSpec.stepList_flatMap_if Guard
    (LengthWrite.positionGates width field key firstWord)
    (positionGates width field key firstWord)
    (position_step_if width field key firstWord)
    (original_position_guard width field key firstWord) _ state

private theorem original_key_guard (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (state : Registers width) :
    Guard (GateSpec.stepList (LengthWrite.gates width field key firstWord) state) ↔
      Guard state := by
  rw [LengthWrite.gates_step]
  split
  · exact constant_guard width field _ state
  · rfl

/-- All actual retained-key calls remain in the emitted list, including inactive keys. -/
def gates (width : Nat) (field : Field) (firstWord : Bool) : List (GateSpec (encoding width)) :=
  (LengthSchedule.keys width).flatMap fun key => keyGates width field key firstWord

/-- The complete enlarged-source schedule equals the original native schedule under its guard. -/
theorem gates_step_if (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    GateSpec.stepList (gates width field firstWord) state =
      if Guard state then GateSpec.stepList (LengthSchedule.gates width field firstWord) state
      else state :=
  GateSpec.stepList_flatMap_if Guard
    (fun key => LengthWrite.gates width field key firstWord)
    (fun key => keyGates width field key firstWord)
    (fun key => key_step_if width field key firstWord)
    (fun key => original_key_guard width field key firstWord) _ state

/-- The independent previously proved full finite register update describes the actual result. -/
theorem gates_step (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    GateSpec.stepList (gates width field firstWord) state =
      if Guard state then LengthSchedule.step width field firstWord state else state := by
  rw [gates_step_if, LengthSchedule.gates_step]

/-- Each original dynamic-boundary schedule retains the exact actual two-field guard. -/
theorem original_guard (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    Guard (GateSpec.stepList (LengthSchedule.gates width field firstWord) state) ↔ Guard state := by
  rw [LengthSchedule.gates_step]
  cases field <;> rfl

/-- The actual program compiled from the enlarged-source lists retains complete basis amplitudes. -/
theorem gates_realizes (width : Nat) (field : Field) (firstWord : Bool) :
    UnitaryCircuit.Realizes (encoding width) (GateSpec.programList (gates width field firstWord))
      (fun state => if Guard state
        then LengthSchedule.step width field firstWord state else state) :=
  GateSpec.realizesList_congrStep _ (gates_step width field firstWord)

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthWrite
