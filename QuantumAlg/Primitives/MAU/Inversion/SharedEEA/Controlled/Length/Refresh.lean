/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Length.Write
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Refresh

/-!
# Actual source-ordered length refresh under retained original Ctrl

The four complete native schedules read coefficient size from Work2 and
then Work1, followed by divisor size from Work1 and then Work2. Ctrl is a
real positive source in every elementary candidate pattern, and original
arbitrary Iter is restored after each candidate
[LYL+26, sec_EEA/sub_regshare.tex:310-314;
LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341].

The actual divisor-length output can change without invalidating this
retained control. The same physical gate list in reverse restores both
lengths in the opposite order. The preceding boundary computation and
word exchange, and the subsequent Iter update and predicate cleanup,
belong to their complete boundary owner.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthRefresh

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit LengthCoordinates

/-- The actual four ordered field/word reads of the source length refresh. -/
def blocks : List (Field × Bool) :=
  [(.coefficient, false), (.coefficient, true), (.divisor, true), (.divisor, false)]

private lemma original_list (width : Nat) :
    (blocks.flatMap fun block => LengthSchedule.gates width block.1 block.2) =
      LengthRefresh.gates width := by
  simp only [blocks, List.flatMap_cons, List.flatMap_nil, LengthRefresh.gates,
    List.append_nil, List.append_assoc]

/-- Every original candidate is replaced by its actual enlarged Ctrl-source pattern. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  blocks.flatMap fun block => ControlledLengthWrite.gates width block.1 block.2

/-- The same complete emitted native list performs the whole original refresh under real Ctrl. -/
lemma gates_step_if (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state =
      if state.control then GateSpec.stepList (LengthRefresh.gates width) state else state := by
  have compared := GateSpec.stepList_flatMap_if
    (fun state : Registers width => state.control = true)
    (fun block : Field × Bool => LengthSchedule.gates width block.1 block.2)
    (fun block : Field × Bool => ControlledLengthWrite.gates width block.1 block.2)
    (fun block => ControlledLengthWrite.gates_step_if width block.1 block.2)
    (fun block state => by rw [ControlledLengthWrite.original_control width block.1 block.2])
    blocks state
  simpa only [gates, original_list] using compared

/-- Complete native-frame semantics is the independent finite LengthPair update under Ctrl. -/
lemma gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state =
      if state.control then LengthRefresh.step state else state := by
  rw [gates_step_if, LengthRefresh.gates_step]

private lemma step_rewind {width : Nat} (state : Registers width) :
    LengthRefresh.step (LengthRefresh.rewind state) = state := by
  change LengthRefresh.withLengths state
    (QuantumAlg.NumberTheory.SharedEEA.LengthPair.update state.firstWord state.secondWord
      (QuantumAlg.NumberTheory.SharedEEA.LengthPair.rewind state.firstWord state.secondWord
        (state.coefficientLength, state.divisorLength))) = state
  rw [QuantumAlg.NumberTheory.SharedEEA.LengthPair.update_rewind]
  rfl

/-- The actual reverse gate list restores the divisor and then the coefficient boundary. -/
lemma gates_reverse_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width).reverse state =
      if state.control then LengthRefresh.rewind state else state := by
  let previous := if state.control then LengthRefresh.rewind state else state
  have forward : GateSpec.stepList (gates width) previous = state := by
    dsimp only [previous]
    by_cases selected : state.control = true
    · rw [if_pos selected, gates_step]
      change (if state.control then LengthRefresh.step (LengthRefresh.rewind state)
        else LengthRefresh.rewind state) = state
      rw [if_pos selected]
      exact step_rewind state
    · rw [if_neg selected, gates_step, if_neg selected]
  calc
    _ = GateSpec.stepList (gates width).reverse (GateSpec.stepList (gates width) previous) :=
      congrArg (GateSpec.stepList (gates width).reverse) forward.symm
    _ = previous := GateSpec.stepList_reverse_stepList (gates width) previous

/-- All fields besides the two length outputs are retained, including arbitrary Iter. -/
lemma gates_retained (width : Nat) (state : Registers width) :
    let result := GateSpec.stepList (gates width) state
    result.firstWord = state.firstWord ∧ result.secondWord = state.secondWord ∧
      result.quotientLength = state.quotientLength ∧ result.shift = state.shift ∧
      result.flags = state.flags ∧ result.control = state.control := by
  dsimp only
  rw [gates_step]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The physical program is precisely the emitted controlled native candidate lists. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

/-- Exact basis realization includes arbitrary incoming Ctrl, source values, and dirty Iter. -/
lemma program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment
      (fun state => if state.control then LengthRefresh.step state else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width) (gates_step width) environment

/-- Every emitted candidate remains in the actual event trace, independently of its input. -/
lemma program_eventTrace (width : Nat) :
    (program width).eventTrace = (gates width).map (GateSpec.event .empty) := by
  rw [program, GateSpec.programList_eventTrace]

/-- Strict unit duration includes the actual four complete candidate schedules. -/
lemma program_unitDepth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = (gates width).length :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthRefresh
