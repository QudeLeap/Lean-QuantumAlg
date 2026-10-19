/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Exchange
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Length.Refresh

/-!
# Actual terminal-aware shared-word boundary program

The native sequence computes the complete-clock boundary condition, swaps
both actual words, refreshes both actual lengths under retained Ctrl,
updates Iter, and reverses the predicate computation. This preserves the
source operation order [LYL+26, sec_EEA/sub_regshare.tex:309-313] while
correcting its finite low-counter boundary test.

The all-input action below explicitly retains the final predicate toggle:
the divisor length and high-clock source positions can change during the
body. Ctrl cleanup is therefore proved on the internally reached selected
boundary, or on the unselected branch, rather than asserted for arbitrary
unreachable frames. The literal reversed gate list restores the complete
original frame on every input, including all lengths and retained history.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalBoundary

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit NativePredicate

/-- The actual controlled body preserves the source order of swap, lengths, and Iter. -/
def body {width : Nat} (state : Registers width) : Registers width :=
  let exchanged := WorkWordExchange.step state
  let refreshed := if exchanged.control then LengthRefresh.step exchanged else exchanged
  BoundaryExchange.parityStep refreshed

/-- Every incoming field, including the possibly changed final predicate, has an exact action. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  let result := body (xorControl (BoundaryPredicate.condition state) state)
  xorControl (BoundaryPredicate.condition result) result

/-- The physical list computes, performs the real boundary body, and uncomputes in reverse. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  BoundaryPredicate.gates width enough ++ WorkWordExchange.gates width ++
    ControlledLengthRefresh.gates width ++ BoundaryExchange.parityGates width ++
    (BoundaryPredicate.gates width enough).reverse

/-- Complete native action, with no omitted last toggle or assumption on incoming Ctrl. -/
lemma gates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough) state = step state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append, GateSpec.stepList_append,
    GateSpec.stepList_append, BoundaryPredicate.gates_step, WorkWordExchange.gates_step,
    ControlledLengthRefresh.gates_step, BoundaryExchange.parityGates_step,
    BoundaryPredicate.reverse_step]
  rfl

/-- Independent complete-word exchange, before the source's length and parity updates. -/
def sourceSwap {width : Nat} (state : Registers width) : Registers width :=
  { state with firstWord := state.secondWord, secondWord := state.firstWord }

/-- Independent source parity update retains both phase flags and Sign. -/
def sourceParity {width : Nat} (state : Registers width) : Registers width :=
  { state with flags := { state.flags with iteration := !state.flags.iteration } }

/-- Independent selected source boundary: exchange, finite lengths, then Iter xor. -/
def sourceBody {width : Nat} (state : Registers width) : Registers width :=
  sourceParity (LengthRefresh.step (sourceSwap state))

private lemma sourceBody_control {width : Nat} (state : Registers width) :
    (sourceBody state).control = state.control := rfl

private lemma body_false {width : Nat} (state : Registers width)
    (clean : state.control = false) : body state = state := by
  unfold body
  have unselected : ¬state.control = true := by
    rw [clean]
    decide
  have exchange : WorkWordExchange.step state = state := by
    simp only [WorkWordExchange.step, if_neg unselected]
  rw [exchange]
  change BoundaryExchange.parityStep
    (if state.control then LengthRefresh.step state else state) = state
  rw [if_neg unselected]
  simp only [BoundaryExchange.parityStep, if_neg unselected]

private lemma body_true {width : Nat} (state : Registers width)
    (selected : state.control = true) : body state = sourceBody state := by
  unfold body
  have exchange : WorkWordExchange.step state = sourceSwap state := by
    simp only [WorkWordExchange.step, selected, if_true, sourceSwap]
  rw [exchange]
  change BoundaryExchange.parityStep
    (if state.control then LengthRefresh.step (sourceSwap state) else sourceSwap state) = _
  rw [if_pos selected]
  change { LengthRefresh.step (sourceSwap state) with flags :=
      { state.flags with iteration := if state.control then !state.flags.iteration
          else state.flags.iteration } } = sourceBody state
  rw [if_pos selected]
  rfl

private lemma sourceBody_xorControl {width : Nat} (value : Bool) (state : Registers width) :
    sourceBody (xorControl value state) = xorControl value (sourceBody state) := rfl

/-- An unselected internally clean branch retains every actual source and history value. -/
lemma step_unselected {width : Nat} (state : Registers width)
    (clean : state.control = false) (unselected : BoundaryPredicate.condition state = false) :
    step state = state := by
  have unchanged : xorControl false state = state := by
    simp only [xorControl, Bool.xor_false]
  dsimp only [step]
  rw [unselected, unchanged, body_false state clean, unselected, unchanged]

/-- The selected branch has its exact final toggle, before any reachable-state cleanup proof. -/
lemma step_selected {width : Nat} (state : Registers width)
    (clean : state.control = false) (selected : BoundaryPredicate.condition state = true) :
    step state = xorControl (BoundaryPredicate.condition (sourceBody state))
      (xorControl true (sourceBody state)) := by
  have control : (xorControl true state).control = true := by
    change (state.control ^^ true) = true
    rw [clean, Bool.false_xor]
  dsimp only [step]
  rw [selected, body_true _ control, sourceBody_xorControl,
    BoundaryPredicate.condition_xorControl]

/-- On an actual reached boundary, preservation of selection discharges the final Ctrl cleanup. -/
lemma step_selected_clean {width : Nat} (state : Registers width)
    (clean : state.control = false) (selected : BoundaryPredicate.condition state = true)
    (after : BoundaryPredicate.condition (sourceBody state) = true) :
    step state = sourceBody state := by
  rw [step_selected state clean selected, after, xorControl_twice]

/-- The whole native boundary restores its internally prepared Ctrl on that selected trajectory. -/
lemma gates_control_selected (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) (clean : state.control = false)
    (selected : BoundaryPredicate.condition state = true)
    (after : BoundaryPredicate.condition (sourceBody state) = true) :
    (GateSpec.stepList (gates width enough) state).control = false := by
  rw [gates_step, step_selected_clean state clean selected after, sourceBody_control, clean]

/-- Literal inverse execution restores both complete words, all finite counts, and all history. -/
lemma reverse_after_forward (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width enough).reverse (GateSpec.stepList (gates width enough) state) =
      state :=
  GateSpec.stepList_reverse_stepList _ _

/-- The unitary is precisely the same actual elementary list on the original full frame. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width enough)

/-- The exact full-input action preserves every relative amplitude and arbitrary correlation. -/
lemma program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough) environment step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width enough) (gates_step width enough) environment

/-- Every predicate, swap, refresh, parity, and inverse-predicate event is present. -/
lemma program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace =
      (gates width enough).map (GateSpec.event .empty) := by
  rw [program, GateSpec.programList_eventTrace]

/-- Exact unit-duration depth includes the full emitted list on all control branches. -/
lemma program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) = (gates width enough).length :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalBoundary
