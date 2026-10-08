/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Length.Write
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Refresh

/-!
# Actual ordered length refresh under the retained source boundary

The four actual enlarged-prefix native schedules execute in the source
order: coefficient from Work2 then Work1, divisor from Work1 then Work2.
The retained quotient and original low-shift bits directly guard every
emitted native predicate [LYL+26, sec_EEA/sub_regshare.tex:309-313;
sec_circuit/sub_block_new.tex:211-219,338-341].

The complete frame action is the independent finite LengthPair update
under that actual guard, with the identity action otherwise. Its literal
reverse gives the corresponding finite inverse. Work-word exchange, the
following Iter update, and terminal-aware padding-clock dispatch remain
separate actual instructions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthRefresh

noncomputable section

open EncodedBit LengthCoordinates GuardedLengthRead

/-- The four actual original source reads in their prescribed sequential order. -/
def blocks : List (Field × Bool) :=
  [(.coefficient, false), (.coefficient, true), (.divisor, true), (.divisor, false)]

private theorem original_list (width : Nat) :
    (blocks.flatMap fun block => LengthSchedule.gates width block.1 block.2) =
      LengthRefresh.gates width := by
  simp only [blocks, List.flatMap_cons, List.flatMap_nil, LengthRefresh.gates,
    List.append_nil, List.append_assoc]

/-- Literal actual native gates with their real added quotient and low-shift source controls. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  blocks.flatMap fun block => GuardedLengthWrite.gates width block.1 block.2

/-- Refinement of the four emitted actual lists retains the source's complete ordered update. -/
theorem gates_step_if (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state =
      if Guard state then GateSpec.stepList (LengthRefresh.gates width) state else state := by
  have compared := GateSpec.stepList_flatMap_if Guard
    (fun block : Field × Bool => LengthSchedule.gates width block.1 block.2)
    (fun block : Field × Bool => GuardedLengthWrite.gates width block.1 block.2)
    (fun block => GuardedLengthWrite.gates_step_if width block.1 block.2)
    (fun block => GuardedLengthWrite.original_guard width block.1 block.2) blocks state
  simpa only [gates, original_list] using compared

/-- Complete actual frame correctness is the independently proved finite update under its guard. -/
theorem gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state =
      if Guard state then LengthRefresh.step state else state := by
  rw [gates_step_if, LengthRefresh.gates_step]

private theorem guard_rewind {width : Nat} (state : Registers width) :
    Guard (LengthRefresh.rewind state) ↔ Guard state := Iff.rfl

private theorem step_rewind {width : Nat} (state : Registers width) :
    LengthRefresh.step (LengthRefresh.rewind state) = state := by
  change LengthRefresh.withLengths state
    (QuantumAlg.NumberTheory.SharedEEA.LengthPair.update state.firstWord state.secondWord
      (QuantumAlg.NumberTheory.SharedEEA.LengthPair.rewind state.firstWord state.secondWord
        (state.coefficientLength, state.divisorLength))) = state
  rw [QuantumAlg.NumberTheory.SharedEEA.LengthPair.update_rewind]
  rfl

/-- The same actual native list in reverse implements the complete guarded finite inverse. -/
theorem gates_reverse_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width).reverse state =
      if Guard state then LengthRefresh.rewind state else state := by
  let previous := if Guard state then LengthRefresh.rewind state else state
  have forward : GateSpec.stepList (gates width) previous = state := by
    dsimp only [previous]
    by_cases guarded : Guard state
    · rw [if_pos guarded, gates_step, if_pos ((guard_rewind state).mpr guarded)]
      exact step_rewind state
    · rw [if_neg guarded, gates_step, if_neg guarded]
  calc
    _ = GateSpec.stepList (gates width).reverse (GateSpec.stepList (gates width) previous) :=
      congrArg (GateSpec.stepList (gates width).reverse) forward.symm
    _ = previous := GateSpec.stepList_reverse_stepList _ _

/-- All complete original register values return under actual forward/inverse composition. -/
theorem reverse_after_forward (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width).reverse (GateSpec.stepList (gates width) state) = state :=
  GateSpec.stepList_reverse_stepList _ _

/-- Original Ctrl is untouched; no clean-control premise is imposed on this actual length kernel. -/
theorem gates_control (width : Nat) (state : Registers width) :
    (GateSpec.stepList (gates width) state).control = state.control := by
  rw [gates_step]
  split <;> rfl

/-- The original arbitrary Iter value used by the actual dirty-work lists is restored exactly. -/
theorem gates_iteration (width : Nat) (state : Registers width) :
    (GateSpec.stepList (gates width) state).flags.iteration = state.flags.iteration := by
  rw [gates_step]
  split <;> rfl

/-- The unitary program is compiled from these actual enlarged-source native lists. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

/-- Complete basis-vector action preserves every untouched coordinate and relative amplitude. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width)
      (fun state => if Guard state then LengthRefresh.step state else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _ (gates_step width)

/-- Every actual native guard and cleanup event remains in the ordered trace. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace = (gates width).map (GateSpec.event .empty) :=
  GateSpec.programList_eventTrace (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthRefresh
