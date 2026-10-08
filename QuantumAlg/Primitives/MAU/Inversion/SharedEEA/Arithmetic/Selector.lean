/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Preservation

/-!
# Actual equality, selected window arithmetic, and inverse equality

A fixed arithmetic selector executes the established physical equality
circuit, the actual Ctrl-selected TTK window, and the reversed equality
list. Its source key includes Sign only for low arithmetic. The full-frame
law below retains arbitrary incoming Ctrl and arbitrary borrowed Iter;
the inactive branch is the identity on every original field.

These fragments refine the actual source arithmetic conditions and windows
[LYL+26, sec_EEA/sub_regshare.tex:278,291-294;
sec_EEA/sub_opt.tex:43-48,61-66]. The window and key here are fixed circuit
parameters. A later finite schedule supplies all possible actual keys;
neither parameter is an input-dependent quantum preparation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelector

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowProgram
open ArithmeticWindowPreservation ArithmeticSelectionKey ArithmeticSelectionPredicate
open NativePredicate

/-- Choose one of the two already implemented actual orientations on the original frame. -/
def bodyStep {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) : Registers width → Registers width :=
  if coefficient then CoefficientWindowProgram.step window operation
  else ArithmeticWindowProgram.step window operation

private def controlledBody {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  if coefficient then CoefficientWindowProgram.controlledProgram window operation
  else ArithmeticWindowControl.program window operation

private def controlledBodyStep {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) : Registers width → Registers width :=
  if coefficient then CoefficientWindowProgram.controlledStep window operation
  else ArithmeticWindowControl.step window operation

private theorem controlledBody_realizes {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool) :
    UnitaryCircuit.Realizes (encoding width) (controlledBody window operation coefficient)
      (controlledBodyStep window operation coefficient) := by
  cases coefficient with
  | false => exact ArithmeticWindowControl.program_realizes window operation
  | true => exact CoefficientWindowProgram.controlledProgram_realizes window operation

private theorem controlledBodyStep_eq_if {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool) (state : Registers width) :
    controlledBodyStep window operation coefficient state =
      if state.control then bodyStep window operation coefficient state else state := by
  cases coefficient with
  | false => exact ArithmeticWindowControl.step_eq_if window operation state
  | true => exact CoefficientWindowProgram.controlledStep_eq_if window operation state

/-- The actual chosen body retains the complete key needed by its own inverse predicate. -/
theorem bodyStep_readKey {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (state : Registers width) :
    readKey width (readsSign operation) (bodyStep window operation coefficient state) =
      readKey width (readsSign operation) state := by
  cases coefficient with
  | false => exact ArithmeticWindowPreservation.remainder_readKey window operation state
  | true => exact ArithmeticWindowPreservation.coefficient_readKey window operation state

private theorem bodyStep_condition {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) (state : Registers width) :
    condition selected (bodyStep window operation coefficient state) =
      condition selected state := by
  simp only [condition, matches_key_iff, bodyStep_readKey]

/-- The ungated selected arithmetic retains arbitrary Ctrl, independently of its initial value. -/
theorem bodyStep_control {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (state : Registers width) :
    (bodyStep window operation coefficient state).control = state.control := by
  cases coefficient with
  | false => exact ArithmeticWindowPreservation.remainder_control window operation state
  | true => exact ArithmeticWindowPreservation.coefficient_control window operation state

/-- The complete selected arithmetic retains arbitrary original Iter as part of the full frame. -/
theorem bodyStep_iteration {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (state : Registers width) :
    (bodyStep window operation coefficient state).flags.iteration = state.flags.iteration := by
  cases coefficient with
  | false => exact ArithmeticWindowPreservation.remainder_iteration window operation state
  | true => exact ArithmeticWindowPreservation.coefficient_iteration window operation state

private theorem bodyStep_xorControl {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (value : Bool) (state : Registers width) :
    bodyStep window operation coefficient (xorControl value state) =
      xorControl value (bodyStep window operation coefficient state) := by
  cases coefficient with
  | false => exact ArithmeticWindowPreservation.remainder_xorControl window operation value state
  | true => exact ArithmeticWindowPreservation.coefficient_xorControl window operation value state

/-- Literal compute/use/uncompute of the fixed actual source equality and native arithmetic. -/
def program {width : Nat} (window : Window width) (operation : Operation) (coefficient : Bool)
    (selected : Key width (readsSign operation)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (ArithmeticSelectionPredicate.program width (readsSign operation) selected).seq
    ((controlledBody window operation coefficient).seq
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (ArithmeticSelectionPredicate.gates width (readsSign operation) selected).reverse))

/-- Exact full-frame result, including both possible incoming Ctrl values. -/
def step {width : Nat} (window : Window width) (operation : Operation) (coefficient : Bool)
    (selected : Key width (readsSign operation)) (state : Registers width) : Registers width :=
  if state.control ^^ condition selected state then
    bodyStep window operation coefficient state else state

private theorem cleanup {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) (state : Registers width) :
    xorControl
        (condition selected (controlledBodyStep window operation coefficient
          (xorControl (condition selected state) state)))
        (controlledBodyStep window operation coefficient
          (xorControl (condition selected state) state)) =
      step window operation coefficient selected state := by
  rw [controlledBodyStep_eq_if]
  change xorControl
    (condition selected (if state.control ^^ condition selected state then
      bodyStep window operation coefficient (xorControl (condition selected state) state)
      else xorControl (condition selected state) state))
    (if state.control ^^ condition selected state then
      bodyStep window operation coefficient (xorControl (condition selected state) state)
      else xorControl (condition selected state) state) = _
  unfold step
  by_cases active : (state.control ^^ condition selected state) = true
  · rw [if_pos active, bodyStep_xorControl, condition_xorControl,
      bodyStep_condition, xorControl_twice, if_pos active]
  · rw [if_neg active, condition_xorControl, xorControl_twice, if_neg active]

/-- The exact selector law follows from the three actual composed native programs. -/
theorem program_realizes {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) :
    UnitaryCircuit.Realizes (encoding width) (program window operation coefficient selected)
      (step window operation coefficient selected) := by
  have actual :=
    (ArithmeticSelectionPredicate.program_realizes width (readsSign operation) selected).seq
      ((controlledBody_realizes window operation coefficient).seq
        (GateSpec.realizesList_congrStep
          (QubitLayout.canonical _) .empty
          (ArithmeticSelectionPredicate.gates width (readsSign operation) selected).reverse
          (ArithmeticSelectionPredicate.reverse_step width (readsSign operation) selected)))
  exact actual.congrStep (cleanup window operation coefficient selected)

/-- Actual predicate cleanup restores the complete original Ctrl for every input frame. -/
theorem step_control {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) (state : Registers width) :
    (step window operation coefficient selected state).control = state.control := by
  unfold step
  split
  · exact bodyStep_control window operation coefficient state
  · rfl

/-- Every actual selector restores arbitrary Iter, including its correlations with other fields. -/
theorem step_iteration {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) (state : Registers width) :
    (step window operation coefficient selected state).flags.iteration = state.flags.iteration := by
  unfold step
  split
  · exact bodyStep_iteration window operation coefficient state
  · rfl

/-- Every source bit used to select this arithmetic remains available to later selectors. -/
theorem step_readKey {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) (state : Registers width) :
    readKey width (readsSign operation) (step window operation coefficient selected state) =
      readKey width (readsSign operation) state := by
  unfold step
  split
  · exact bodyStep_readKey window operation coefficient state
  · rfl

/-- A nonmatching fixed key is exactly inactive on an internally initialized Ctrl-zero frame. -/
theorem step_inactive {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) (state : Registers width)
    (clean : state.control = false)
    (different : selected ≠ readKey width (readsSign operation) state) :
    step window operation coefficient selected state = state := by
  rw [step, clean, condition_false_of_ne width (readsSign operation) selected state different]
  rfl

/-- The unique matching key executes precisely its chosen actual arithmetic body. -/
theorem step_matching {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (state : Registers width) (clean : state.control = false) :
    step window operation coefficient (readKey width (readsSign operation) state) state =
      bodyStep window operation coefficient state := by
  rw [step, clean, condition_readKey]
  rfl

/-- Exact trace includes both real equality computations and the actual selected TTK list. -/
theorem program_eventTrace {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (program window operation coefficient selected).eventTrace =
      (ArithmeticSelectionPredicate.gates width (readsSign operation) selected).map
        (GateSpec.event .empty) ++
      (ArithmeticWindowControl.gates window operation).map (GateSpec.event .empty) ++
      (ArithmeticSelectionPredicate.gates width (readsSign operation) selected).reverse.map
        (GateSpec.event .empty) := by
  cases coefficient <;> simp only [program, controlledBody, Bool.false_eq_true, if_false, if_true,
    UnitaryCircuit.seq_eventTrace, GateSpec.programList_eventTrace,
    ArithmeticSelectionPredicate.program, ArithmeticWindowControl.program_eventTrace,
    CoefficientWindowProgram.controlledProgram_eventTrace, List.append_assoc]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelector
