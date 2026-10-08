/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Instruction

/-!
# Complete actual finite schedules for the source arithmetic instructions

Every complete actual length/phase pattern occurs once. Each fixed pattern
contributes its already implemented native compute/use/uncompute program
at its original physical window. The schedule is fixed independently of
the quantum input, including at zero finite-field width. No quantum input
is replaced by a classical callback or an input-dependent preparation.

Preservation of the actual readout key makes every nonmatching selector
inactive and lets the unique matching selector execute once on internally
initialized Ctrl-zero frames. The resulting action is the independent
source operation [LYL+26, sec_EEA/sub_regshare.tex:278,291-294;
sec_EEA/sub_opt.tex:43-48,61-66]. Complete arbitrary-Ctrl realization and
the actual event trace remain separate from that initialized specialization.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSchedule

noncomputable section

open ArithmeticSelectionKey ArithmeticInstruction

private def listProgram (width : Nat) (instruction : Instruction) :
    List (Key width (includeSign instruction)) →
      UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical (encoding width).width).toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model .empty (QubitLayout.canonical _).toQuantum
  | selected :: rest =>
      (ArithmeticInstruction.program width instruction selected).seq
        (listProgram width instruction rest)

private theorem listProgram_realizes (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    UnitaryCircuit.Realizes (encoding width) (listProgram width instruction indices)
      (fun state => indices.foldl
        (fun current selected => ArithmeticInstruction.step width instruction selected current)
        state) := by
  induction indices with
  | nil =>
      exact UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
        (encoding width) (QubitLayout.canonical _)
  | cons selected rest ih =>
      exact (ArithmeticInstruction.program_realizes width instruction selected).seq ih

private theorem fold_control (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) (state : Registers width) :
    (indices.foldl
      (fun current selected => ArithmeticInstruction.step width instruction selected current)
      state).control = state.control := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, ih, ArithmeticInstruction.step_control]

private theorem fold_iteration (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) (state : Registers width) :
    (indices.foldl
      (fun current selected => ArithmeticInstruction.step width instruction selected current)
      state).flags.iteration = state.flags.iteration := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, ih, ArithmeticInstruction.step_iteration]

private theorem fold_readKey (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) (state : Registers width) :
    readKey width (includeSign instruction)
      (indices.foldl
        (fun current selected => ArithmeticInstruction.step width instruction selected current)
        state) = readKey width (includeSign instruction) state := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, ih, ArithmeticInstruction.step_readKey]

private theorem fold_inactive (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction)))
    (state : Registers width) (clean : state.control = false)
    (inactive : ∀ selected, selected ∈ indices →
      selected ≠ readKey width (includeSign instruction) state) :
    indices.foldl
      (fun current selected => ArithmeticInstruction.step width instruction selected current)
      state = state := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, ArithmeticInstruction.step_inactive width instruction selected state
        clean (inactive selected List.mem_cons_self)]
      exact ih (fun other present => inactive other (List.mem_cons_of_mem _ present))

private theorem fold_once (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    ∀ state : Registers width, state.control = false → indices.Nodup →
      indices.foldl
        (fun current selected => ArithmeticInstruction.step width instruction selected current)
        state =
        if readKey width (includeSign instruction) state ∈ indices then
          ArithmeticInstruction.step width instruction
            (readKey width (includeSign instruction) state) state else state := by
  induction indices with
  | nil =>
      intro state _clean _unique
      simp only [List.foldl_nil, List.not_mem_nil, if_false]
  | cons selected rest ih =>
      intro state clean unique
      rw [List.foldl_cons]
      by_cases same : selected = readKey width (includeSign instruction) state
      · subst selected
        have inactive : ∀ other, other ∈ rest →
            other ≠ readKey width (includeSign instruction)
              (ArithmeticInstruction.step width instruction
                (readKey width (includeSign instruction) state) state) := by
          intro other present
          rw [ArithmeticInstruction.step_readKey]
          intro equal
          subst other
          exact unique.notMem present
        rw [fold_inactive width instruction rest _
          ((ArithmeticInstruction.step_control width instruction _ state).trans clean) inactive,
          if_pos List.mem_cons_self]
      · rw [ArithmeticInstruction.step_inactive width instruction selected state clean same,
          ih state clean unique.tail]
        simp only [List.mem_cons, Ne.symm same, false_or]

/-- Execute the actual fixed native program for every complete source key once. -/
def program (width : Nat) (instruction : Instruction) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  listProgram width instruction (keys width (includeSign instruction))

/-- Complete frame action of that actual finite instruction schedule. -/
def step (width : Nat) (instruction : Instruction) (state : Registers width) : Registers width :=
  (keys width (includeSign instruction)).foldl
    (fun current selected => ArithmeticInstruction.step width instruction selected current) state

/-- The actual quantum schedule has exact complete-frame basis amplitudes on every input. -/
theorem program_realizes (width : Nat) (instruction : Instruction) :
    UnitaryCircuit.Realizes (encoding width) (program width instruction) (step width instruction) :=
  listProgram_realizes width instruction _

/-- All actual selectors restore the original Ctrl, including a nonzero incoming Ctrl. -/
theorem step_control (width : Nat) (instruction : Instruction) (state : Registers width) :
    (step width instruction state).control = state.control := fold_control width instruction _ state

/-- The complete actual finite schedule restores arbitrary Iter and its full frame correlations. -/
theorem step_iteration (width : Nat) (instruction : Instruction) (state : Registers width) :
    (step width instruction state).flags.iteration = state.flags.iteration :=
  fold_iteration width instruction _ state

/-- Every actual source bit used by this instruction is unchanged after its complete schedule. -/
theorem step_readKey (width : Nat) (instruction : Instruction) (state : Registers width) :
    readKey width (includeSign instruction) (step width instruction state) =
      readKey width (includeSign instruction) state := fold_readKey width instruction _ state

/-- The internally initialized schedule executes exactly its one actual matching selector. -/
theorem step_prepared (width : Nat) (instruction : Instruction) (state : Registers width)
    (clean : state.control = false) :
    step width instruction state = ArithmeticInstruction.step width instruction
      (readKey width (includeSign instruction) state) state := by
  have actual := fold_once width instruction (keys width (includeSign instruction)) state clean
    (keys_nodup width (includeSign instruction))
  rw [if_pos (key_mem width (includeSign instruction) _)] at actual
  exact actual

/-- The actual complete schedule refines the independent current-field source instruction. -/
theorem step_eq_source (width : Nat) (instruction : Instruction) (state : Registers width)
    (clean : state.control = false) :
    step width instruction state = ArithmeticInstruction.sourceStep instruction state := by
  rw [step_prepared width instruction state clean,
    ArithmeticInstruction.step_matching width instruction state clean,
    ArithmeticInstruction.selectedBody_readKey]

/-- Exact basis action of the actual schedule on the algorithm's internally prepared frames. -/
theorem program_apply_prepared (width : Nat) (instruction : Instruction) (state : Registers width)
    (clean : state.control = false) :
    (program width instruction).applyNormalized
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (ArithmeticInstruction.sourceStep instruction state))) := by
  rw [(program_realizes width instruction).apply_encoded_ket, step_eq_source width instruction state
    clean]

private theorem listProgram_eventTrace (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    (listProgram width instruction indices).eventTrace =
      indices.flatMap (fun selected =>
        (ArithmeticInstruction.program width instruction selected).eventTrace) := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [listProgram, UnitaryCircuit.seq_eventTrace, ih, List.flatMap_cons]

/-- Exact trace of the fixed schedule retains all emitted predicates, arithmetic, and cleanup. -/
theorem program_eventTrace (width : Nat) (instruction : Instruction) :
    (program width instruction).eventTrace =
      (keys width (includeSign instruction)).flatMap (fun selected =>
        (ArithmeticInstruction.program width instruction selected).eventTrace) :=
  listProgram_eventTrace width instruction _

/-- The schedule enumerates exactly the finite source-key count, including all leading-zero keys. -/
theorem selector_count (width : Nat) (instruction : Instruction) :
    (keys width (includeSign instruction)).length =
      2 ^ ArithmeticSelectionLayout.sourceCount width (includeSign instruction) :=
  keys_length width (includeSign instruction)

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSchedule
