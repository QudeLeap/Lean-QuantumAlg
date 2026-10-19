/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Fintype.BigOperators
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Schedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Resources

/-!
# Actual arithmetic selector schedule after complete coefficient comparison

The actual equality layout reads all four existing length words, the two
phase bits, and Sign only when the arithmetic retains it. Reading the
existing divisor boundary permits the full aligned coefficient comparison
[LYL+26, sec_EEA/sub_regshare.tex:263-264,297-300]. No quantum register is
allocated for finite enumeration keys.

The bounds below count both real predicate lists and the actual controlled
TTK arithmetic for every emitted selector, including cleanup of arbitrary
Iter. Invalid windows emit the existing empty identity. These are bounds
for the present finite native schedule, not the paper's original whole-EEA
asymptotic count or a claim about unproved terminal dispatch.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticScheduleResources

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowProgram ArithmeticWindowPreservation
open ArithmeticSelectionKey ArithmeticInstruction

/-- Uniform elementary-gate bound for both predicates and the actual full-word arithmetic. -/
def selectorBound (width : Nat) (includeSign : Bool) : Nat :=
  20 * ArithmeticSelectionLayout.sourceCount width includeSign + 28 * (width + 3) + 10

/-- The selector trace includes both full pattern computations and the controlled TTK list. -/
lemma selector_trace_le {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (ArithmeticSelector.program window operation coefficient selected).eventTrace.length ≤
      selectorBound width (readsSign operation) := by
  rw [ArithmeticSelector.program_eventTrace]
  simp only [List.length_append, List.length_map, List.length_reverse]
  have predicate := ArithmeticSelectionPredicate.gates_length_le width
    (readsSign operation) selected
  have body := ArithmeticWindowResources.controlledGates_length_le_frame window operation
  unfold selectorBound
  omega

/-- Unit event depth of this strictly sequential selector is its actual emitted event count. -/
lemma selector_depth_eq_trace {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (ArithmeticSelector.program window operation coefficient selected).evaluatedEventDepth
        (fun _ => 1) =
      (ArithmeticSelector.program window operation coefficient selected).eventTrace.length := by
  rw [ArithmeticSelector.program_eventTrace]
  cases coefficient <;>
    simp only [ArithmeticSelector.program, ArithmeticSelector.controlledBody,
      Bool.false_eq_true, if_false, if_true, UnitaryCircuit.evaluatedEventDepth_seq,
      ArithmeticSelectionPredicate.program_unitDepth,
      ArithmeticWindowResources.remainder_unitDepth,
      ArithmeticWindowResources.coefficient_unitDepth,
      GateSpec.programList_evaluatedEventDepth_unit,
      List.length_append, List.length_map, List.length_reverse, Nat.add_assoc]

/-- Every actual instruction has the same bound, including disabled and invalid-window keys. -/
lemma instruction_trace_le (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    (ArithmeticInstruction.program width instruction selected).eventTrace.length ≤
      selectorBound width (includeSign instruction) := by
  unfold ArithmeticInstruction.program
  split
  · cases choice : selectedWindow instruction selected with
    | none => exact Nat.zero_le _
    | some window =>
        exact selector_trace_le window (operation instruction) (coefficient instruction) selected
  · exact Nat.zero_le _

/-- The strict depth of each emitted instruction is its actual event trace length. -/
lemma instruction_depth_eq_trace (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    (ArithmeticInstruction.program width instruction selected).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticInstruction.program width instruction selected).eventTrace.length := by
  unfold ArithmeticInstruction.program
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window =>
        exact selector_depth_eq_trace window (operation instruction)
          (coefficient instruction) selected
  · rfl

/-- The real first phase coordinate has exactly half of the complete actual keys. -/
lemma first_key_card (width : Nat) (includeSign : Bool) (value : Bool) :
    Fintype.card {selected : Key width includeSign // first selected = value} =
      2 ^ (ArithmeticSelectionLayout.sourceCount width includeSign - 1) := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun selected :
    Fin (ArithmeticSelectionLayout.sourceCount width includeSign) → Bool =>
      selected (ArithmeticSelectionKey.firstIndex width includeSign) = value)).card = _
  have counted := Fintype.card_filter_piFinset_const_eq_of_mem
    (Finset.univ : Finset Bool) (ArithmeticSelectionKey.firstIndex width includeSign)
    (Finset.mem_univ value)
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_bool,
    Fintype.card_fin] using counted

/-- Static rejection never enables an arithmetic body in the opposite real first phase. -/
lemma enabled_first {width : Nat} (instruction : Instruction)
    (selected : Key width (includeSign instruction))
    (active : enabled instruction selected = true) :
    first selected = ArithmeticInstruction.coefficient instruction := by
  cases instruction <;> cases phase : first selected <;>
    simp [enabled, ArithmeticInstruction.phaseEnabled, ArithmeticInstruction.coefficient,
      phase] at active ⊢

/-- Complete enumeration converts a filtered actual-key list to its subtype cardinality. -/
lemma keys_filter_length (width : Nat) (includeSign : Bool)
    (predicate : Key width includeSign → Prop) [DecidablePred predicate] :
    ((keys width includeSign).filter (fun selected => decide (predicate selected))).length =
      Fintype.card {selected : Key width includeSign // predicate selected} := by
  classical
  have counted := (keys_nodup width includeSign).card_eq_countP (P := predicate)
  rw [List.countP_eq_length_filter] at counted
  have complete : (keys width includeSign).toFinset = Finset.univ := by
    ext selected
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact key_mem width includeSign selected
  calc
    _ = ((keys width includeSign).toFinset.filter predicate).card := counted.symm
    _ = (Finset.univ.filter predicate).card := by rw [complete]
    _ = Fintype.card {selected : Key width includeSign // predicate selected} :=
      (Fintype.card_subtype predicate).symm

/-- The real enumeration retains its original order; only its matching phase is counted. -/
lemma keys_first_length (width : Nat) (includeSign : Bool) (value : Bool) :
    ((keys width includeSign).filter
      (fun selected => decide (first selected = value))).length =
        2 ^ (ArithmeticSelectionLayout.sourceCount width includeSign - 1) := by
  rw [keys_filter_length, first_key_card]

/-- An opposite-phase actual key emits the existing empty identity trace. -/
lemma instruction_trace_eq_nil_of_wrong_first (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction))
    (wrong : first selected ≠ ArithmeticInstruction.coefficient instruction) :
    (ArithmeticInstruction.program width instruction selected).eventTrace = [] := by
  have disabled : enabled instruction selected = false := by
    cases active : enabled instruction selected with
    | false => rfl
    | true => exact False.elim (wrong (enabled_first instruction selected active))
  simp [ArithmeticInstruction.program, disabled, ArithmeticInstruction.identity]

private lemma list_trace_le (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    (indices.flatMap fun selected =>
      (ArithmeticInstruction.program width instruction selected).eventTrace).length ≤
        (indices.filter (fun selected => decide
          (first selected = ArithmeticInstruction.coefficient instruction))).length *
            selectorBound width (includeSign instruction) := by
  induction indices with
  | nil => simp
  | cons selected rest ih =>
      rw [List.flatMap_cons, List.length_append]
      by_cases phase : first selected = ArithmeticInstruction.coefficient instruction
      · simp only [List.filter_cons, decide_eq_true phase, if_true, List.length_cons,
          Nat.add_mul, Nat.one_mul]
        have current := instruction_trace_le width instruction selected
        omega
      · rw [instruction_trace_eq_nil_of_wrong_first width instruction selected phase]
        simpa only [List.length_nil, Nat.zero_add, List.filter_cons,
          decide_eq_false phase, Bool.false_eq_true, if_false] using ih

private lemma list_depth_eq_trace (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    (ArithmeticSchedule.listProgram width instruction indices).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticSchedule.listProgram width instruction indices).eventTrace.length := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [ArithmeticSchedule.listProgram, UnitaryCircuit.evaluatedEventDepth_seq,
        UnitaryCircuit.seq_eventTrace, List.length_append,
        instruction_depth_eq_trace, ih]

/-- The exact revised enumeration counts all four real length words and actual source flags. -/
lemma selector_count (width : Nat) (instruction : Instruction) :
    (ArithmeticSelectionKey.keys width (includeSign instruction)).length =
      2 ^ (4 * width.size + 2 + if includeSign instruction then 1 else 0) :=
  ArithmeticSchedule.selector_count width instruction

/-- Actual trace size includes every emitted selector and both predicate computations. -/
lemma program_trace_le (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).eventTrace.length ≤
      2 ^ ((4 * width.size + 2 + if includeSign instruction then 1 else 0) - 1) *
        selectorBound width (includeSign instruction) := by
  rw [ArithmeticSchedule.program_eventTrace]
  have actual := list_trace_le width instruction
    (ArithmeticSelectionKey.keys width (includeSign instruction))
  rw [keys_first_length] at actual
  exact actual

/-- Strict unit duration depth counts the same actual sequential native trace. -/
lemma program_depth_eq_trace (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticSchedule.program width instruction).eventTrace.length :=
  list_depth_eq_trace width instruction
    (ArithmeticSelectionKey.keys width (includeSign instruction))

/-- The independent selector envelope therefore bounds the actual complete native depth. -/
lemma program_depth_le (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).evaluatedEventDepth (fun _ => 1) ≤
      2 ^ ((4 * width.size + 2 + if includeSign instruction then 1 else 0) - 1) *
        selectorBound width (includeSign instruction) := by
  rw [program_depth_eq_trace]
  exact program_trace_le width instruction

/-- The same trace derives the literal resource pool; no independent cost witness is accepted. -/
lemma program_pool (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).eventCost = ResourcePool.ofList
      (ArithmeticSchedule.program width instruction).eventTrace :=
  (UnitaryCircuit.ofList_eventTrace_eq_eventCost _).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticScheduleResources
