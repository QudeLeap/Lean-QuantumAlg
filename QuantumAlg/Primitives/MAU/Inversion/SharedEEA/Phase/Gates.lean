/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout

/-!
# Actual native gates for the ordered shared-EEA phase assignments

The source first XORs Sign and Phase1 into Phase2, then XORs the updated
Phase2 into Sign [LYL+26, sec_EEA/sub_regshare.tex:303-305;
sec_EEA/sub_opt.tex:74-76]. This owner compiles those three ordered XORs
to three actual Toffoli gates controlled by the separately declared Ctrl
wire [LYL+26, sec_EEA/sub_regshare.tex:25-26]. It also implements the two
phase complements as two controlled native flips.

The specifications hold for every full register label, including arbitrary
Ctrl and entangled superpositions after linear extension. They preserve
both work words, every finite length, Iter, and Ctrl. Computing the actual
length predicates into Ctrl and reversing that computation are separate
gate refinements; this local kernel makes no assumption that Ctrl already
equals a source predicate. It does not implement a whole EEA microstep or
claim a whole-algorithm resource bound.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PhaseGates

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private theorem phase1_phase2_ne (width : Nat) :
    (phase1Bit width).wire ≠ (phase2Bit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase1Bit_wire, phase2Bit_wire] at values
  omega

private theorem phase2_sign_ne (width : Nat) :
    (phase2Bit width).wire ≠ (signBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase2Bit_wire, signBit_wire] at values
  omega

private theorem control_phase1_ne (width : Nat) :
    (controlBit width).wire ≠ (phase1Bit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [controlBit_wire, phase1Bit_wire] at values
  omega

private theorem control_phase2_ne (width : Nat) :
    (controlBit width).wire ≠ (phase2Bit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [controlBit_wire, phase2Bit_wire] at values
  omega

private theorem control_sign_ne (width : Nat) :
    (controlBit width).wire ≠ (signBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [controlBit_wire, signBit_wire] at values
  omega

/-- Three actual Toffoli gates, in the source's sequential assignment order. -/
def updateGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.toffoli (controlBit width) (signBit width) (phase2Bit width)
      (control_sign_ne width) (control_phase2_ne width) (phase2_sign_ne width).symm,
    .toffoli (controlBit width) (phase1Bit width) (phase2Bit width)
      (control_phase1_ne width) (control_phase2_ne width) (phase1_phase2_ne width),
    .toffoli (controlBit width) (phase2Bit width) (signBit width)
      (control_phase2_ne width) (control_sign_ne width) (phase2_sign_ne width)]

/-- Mathematical phase update selected by the existing Ctrl bit, on the full register state. -/
def updateStep {width : Nat} (state : Registers width) : Registers width :=
  { state with flags :=
      if state.control then PhaseControl.update true true false state.flags else state.flags }

/-- The literal gates implement the ordered mathematical assignments on every register label. -/
theorem updateGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (updateGates width) state = updateStep state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨phase1, phase2, sign, iteration⟩, control⟩
  cases phase1 <;> cases phase2 <;> cases sign <;> cases control <;> rfl

/-- Compile the actual controlled XOR list; no permutation is declared as an opaque gate. -/
def updateProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  GateSpec.programList (updateGates width)

/-- Exact basis-vector semantics of the same native program used for accounting. -/
theorem updateProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (updateProgram width) updateStep :=
  GateSpec.realizesList_congrStep (updateGates width) (updateGates_step width)

/-- All non-target fields are preserved, including the independent source Ctrl bit. -/
theorem updateStep_retained {width : Nat} (state : Registers width) :
    (updateStep state).firstWord = state.firstWord ∧
      (updateStep state).secondWord = state.secondWord ∧
      (updateStep state).coefficientLength = state.coefficientLength ∧
      (updateStep state).quotientLength = state.quotientLength ∧
      (updateStep state).divisorLength = state.divisorLength ∧
      (updateStep state).shift = state.shift ∧
      (updateStep state).flags.iteration = state.flags.iteration ∧
      (updateStep state).control = state.control := by
  cases selected : state.control <;> simp [updateStep, selected, PhaseControl.update]

/-- Reversing those same three native gates restores every field for arbitrary input. -/
theorem updateGates_reverse {width : Nat} (state : Registers width) :
    GateSpec.stepList (updateGates width).reverse (updateStep state) = state := by
  rw [← updateGates_step]
  exact GateSpec.stepList_reverse_stepList (updateGates width) state

/-- The actual program emits precisely three Toffoli events, even when Ctrl is false. -/
theorem updateProgram_eventTrace (width : Nat) :
    (updateProgram width).eventTrace =
      [.gate (.builtin "toffoli"), .gate (.builtin "toffoli"),
        .gate (.builtin "toffoli")] := by
  rw [updateProgram, GateSpec.programList_eventTrace]
  rfl

theorem updateProgram_eventCost_card (width : Nat) :
    (updateProgram width).eventCost.card = 3 :=
  GateSpec.programList_eventCost_card (updateGates width)

theorem updateProgram_unitDepth (width : Nat) :
    (updateProgram width).evaluatedEventDepth (fun _ => 1) = 3 :=
  GateSpec.programList_evaluatedEventDepth_unit (updateGates width)

/-- The zero-shift phase-complement kernel uses two actual CNOT gates controlled by Ctrl. -/
def complementGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.cnot (controlBit width) (phase1Bit width) (control_phase1_ne width),
    .cnot (controlBit width) (phase2Bit width) (control_phase2_ne width)]

/-- Complement exactly the two phase bits if the retained control is one. -/
def complementStep {width : Nat} (state : Registers width) : Registers width :=
  { state with flags :=
      ⟨if state.control then !state.flags.first else state.flags.first,
        if state.control then !state.flags.second else state.flags.second,
        state.flags.sign, state.flags.iteration⟩ }

theorem complementGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (complementGates width) state = complementStep state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨phase1, phase2, sign, iteration⟩, control⟩
  cases control <;> rfl

def complementProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  GateSpec.programList (complementGates width)

theorem complementProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (complementProgram width) complementStep :=
  GateSpec.realizesList_congrStep (complementGates width) (complementGates_step width)

theorem complementGates_reverse {width : Nat} (state : Registers width) :
    GateSpec.stepList (complementGates width).reverse (complementStep state) = state := by
  rw [← complementGates_step]
  exact GateSpec.stepList_reverse_stepList (complementGates width) state

/-- Both physical CNOT events remain in the trace for every input control value. -/
theorem complementProgram_eventTrace (width : Nat) :
    (complementProgram width).eventTrace =
      [.gate (.builtin "cnot"), .gate (.builtin "cnot")] := by
  rw [complementProgram, GateSpec.programList_eventTrace]
  rfl

theorem complementProgram_eventCost_card (width : Nat) :
    (complementProgram width).eventCost.card = 2 :=
  GateSpec.programList_eventCost_card (complementGates width)

theorem complementProgram_unitDepth (width : Nat) :
    (complementProgram width).evaluatedEventDepth (fun _ => 1) = 2 :=
  GateSpec.programList_evaluatedEventDepth_unit (complementGates width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.PhaseGates
