/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Schedule
import all QuantumAlg.Util.NumberTheory.SharedEEA.Length.Pair

/-!
# Actual ordered refresh of both original shared-EEA length registers

The original work words have already been exchanged when this instruction
is called. The coefficient field first XORs the old size read from Work2,
then the new size read from Work1. The divisor field subsequently XORs its
old Work1 size and new Work2 size at the newly updated coefficient boundary
[LYL+26, sec_EEA/sub_regshare.tex:309-313;
sec_circuit/sub_block_new.tex:211-219,338-341].

All four operations below are the actual fixed native gate schedules, with
their full boundary and leading-position enumerations. Their full-register
action equals the previously proved finite mathematical LengthPair update
on every input. In particular the reverse list restores the divisor field
first and uses that restored boundary for the inverse coefficient writes.
The preceding word exchange and subsequent Iter update are separate actual
instructions and are not included in this gate list.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthRefresh

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit

/-- Replace exactly the two actual retained length fields by a finite pair. -/
def withLengths {width : Nat} (state : Registers width)
    (lengths : BitVec width.size × BitVec width.size) : Registers width :=
  { state with coefficientLength := lengths.1, divisorLength := lengths.2 }

/-- Complete frame action of the source's previously proved ordered finite length refresh. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  withLengths state (QuantumAlg.NumberTheory.SharedEEA.LengthPair.update
    state.firstWord state.secondWord (state.coefficientLength, state.divisorLength))

/-- The inverse frame action uses the recovered divisor boundary to restore the coefficient. -/
def rewind {width : Nat} (state : Registers width) : Registers width :=
  withLengths state (QuantumAlg.NumberTheory.SharedEEA.LengthPair.rewind
    state.firstWord state.secondWord (state.coefficientLength, state.divisorLength))

/-- These four dynamic native reads occur in the actual source order at their actual boundaries. -/
lemma ordered_steps (width : Nat) (state : Registers width) :
    LengthSchedule.step width .divisor false
      (LengthSchedule.step width .divisor true
        (LengthSchedule.step width .coefficient true
          (LengthSchedule.step width .coefficient false state))) = step state := by
  rfl

/-- Reversing the native reads first restores the divisor and then the coefficient boundary. -/
lemma reverse_ordered_steps (width : Nat) (state : Registers width) :
    LengthSchedule.step width .coefficient false
      (LengthSchedule.step width .coefficient true
        (LengthSchedule.step width .divisor true
          (LengthSchedule.step width .divisor false state))) = rewind state := by
  rfl

/-- Literal actual native gate list, including every boundary and leading-position call. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  LengthSchedule.gates width .coefficient false ++
    LengthSchedule.gates width .coefficient true ++
    LengthSchedule.gates width .divisor true ++
    LengthSchedule.gates width .divisor false

/-- The same complete actual list implements the exact finite LengthPair update on all frames. -/
lemma gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state = step state := by
  simp only [gates, GateSpec.stepList_append, LengthSchedule.gates_step]
  exact ordered_steps width state

/-- The literal reversed elementary list implements the exact finite inverse LengthPair update. -/
lemma gates_reverse_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width).reverse state = rewind state := by
  simp only [gates, List.reverse_append, GateSpec.stepList_append,
    LengthSchedule.gates_reverse_step]
  exact reverse_ordered_steps width state

/-- Actual forward and reverse lists restore the entire arbitrary incoming register frame. -/
lemma reverse_after_forward (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width).reverse (GateSpec.stepList (gates width) state) = state :=
  GateSpec.stepList_reverse_stepList _ _

/-- The finite mathematical inverse is therefore realized by the actual original-frame gates. -/
lemma rewind_step {width : Nat} (state : Registers width) : rewind (step state) = state := by
  have actual := reverse_after_forward width state
  rw [gates_step, gates_reverse_step] at actual
  exact actual

/-- Both full work words and every field besides the two updated lengths are retained. -/
lemma gates_retained (width : Nat) (state : Registers width) :
    let result := GateSpec.stepList (gates width) state
    result.firstWord = state.firstWord ∧ result.secondWord = state.secondWord ∧
      result.quotientLength = state.quotientLength ∧ result.shift = state.shift ∧
      result.flags = state.flags ∧ result.control = state.control := by
  dsimp only
  rw [gates_step]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The circuit is the actual elementary program list, with no additional native declaration. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

/-- Complete basis action of the actual program agrees with the independent finite update. -/
lemma program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width) (gates_step width) environment

/-- Actual ordered events retain all four complete native write schedules. -/
lemma program_eventTrace (width : Nat) :
    (program width).eventTrace = (gates width).map (GateSpec.event .empty) := by
  rw [program, GateSpec.programList_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthRefresh
