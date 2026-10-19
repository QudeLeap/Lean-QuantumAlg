/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.WorkWordExchange

/-!
# Actual boundary predicate, shared-word exchange, and parity update

The source exchanges both words and complements Iter at the joint condition
that quotient length and shift are zero [LYL+26, sec_EEA/sub_opt.tex:81-84].
This native kernel computes that exact retained-field predicate into Ctrl,
performs the complete word exchange and one Iter CNOT, and reverses the
predicate. The zero-test theorem restores arbitrary borrowed Work2 values,
so its inverse cleanup remains valid after the words have exchanged.

The complete action allows arbitrary incoming Ctrl and retains it exactly.
Its internally prepared-zero specialization has the source exchange/parity
action. Both coefficient and divisor length fields remain unchanged in this
kernel: their actual refresh is a separate required operation. Consequently
this owner is not a complete boundary transition or a completed EEA round.
The repaired terminal counter dispatch also remains separate from this
original low-counter boundary test.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.BoundaryExchange

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit NativePredicate

/-- The original boundary predicate reads the two actual retained finite fields. -/
def condition {width : Nat} (state : Registers width) : Bool :=
  decide (state.quotientLength = 0 ∧ state.shift = 0)

private lemma condition_xorControl {width : Nat} (value : Bool) (state : Registers width) :
    condition (xorControl value state) = condition state := rfl

/-- Actual joint zero-predicate gates, with the complete borrowed Work2 restored. -/
def conditionGates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  pairGates width .quotient .shift (by decide) enough

private lemma conditionGates_step (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) :
    GateSpec.stepList (conditionGates width enough) state = xorControl (condition state) state :=
  pairGates_step width .quotient .shift (by decide) enough state

private lemma conditionGates_reverse_step (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) :
    GateSpec.stepList (conditionGates width enough).reverse state =
      xorControl (condition state) state := by
  let toggled := xorControl (condition state) state
  have forward : GateSpec.stepList (conditionGates width enough) toggled = state := by
    rw [conditionGates_step]
    change xorControl (condition (xorControl (condition state) state))
      (xorControl (condition state) state) = state
    rw [condition_xorControl, xorControl_twice]
  calc
    GateSpec.stepList (conditionGates width enough).reverse state =
        GateSpec.stepList (conditionGates width enough).reverse
          (GateSpec.stepList (conditionGates width enough) toggled) :=
      congrArg (GateSpec.stepList (conditionGates width enough).reverse) forward.symm
    _ = toggled := GateSpec.stepList_reverse_stepList (conditionGates width enough) toggled

private lemma control_iteration (width : Nat) :
    (controlBit width).wire ≠ (iterationBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [controlBit_wire, iterationBit_wire] at values
  omega

/-- One actual CNOT updates the retained iteration parity. -/
def parityGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.cnot (controlBit width) (iterationBit width) (control_iteration width)]

private def parityStep {width : Nat} (state : Registers width) : Registers width :=
  { state with flags := { state.flags with
      iteration := if state.control then !state.flags.iteration else state.flags.iteration } }

private lemma parityGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (parityGates width) state = parityStep state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iteration⟩, control⟩
  cases control <;> rfl

/-- Complete exchange/parity action, using the computed xor and preserving the incoming Ctrl. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  { state with
    firstWord := if state.control ^^ condition state then state.secondWord else state.firstWord
    secondWord := if state.control ^^ condition state then state.firstWord else state.secondWord
    flags := { state.flags with iteration :=
      if state.control ^^ condition state then !state.flags.iteration else state.flags.iteration } }

private lemma condition_step {width : Nat} (state : Registers width) :
    condition (step state) = condition state := rfl

private lemma body_computed {width : Nat} (state : Registers width) :
    parityStep (WorkWordExchange.step (xorControl (condition state) state)) =
      xorControl (condition state) (step state) := rfl

/-- Both predicate passes surround the actual full-word swap and the actual parity CNOT. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  conditionGates width enough ++ WorkWordExchange.gates width ++ parityGates width ++
    (conditionGates width enough).reverse

/-- The whole native sequence has the complete frame action, including inverse Ctrl cleanup. -/
lemma gates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough) state = step state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append, GateSpec.stepList_append,
    conditionGates_step, WorkWordExchange.gates_step, parityGates_step, body_computed,
    conditionGates_reverse_step, condition_xorControl, condition_step, xorControl_twice]

/-- The original Ctrl is restored even after arbitrary complete words have exchanged. -/
lemma gates_control (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    (GateSpec.stepList (gates width enough) state).control = state.control := by
  rw [gates_step]
  rfl

/-- The source's exchange and parity operations, with length refresh still to be performed. -/
def sourceStep {width : Nat} (state : Registers width) : Registers width :=
  { state with
    firstWord := if condition state then state.secondWord else state.firstWord
    secondWord := if condition state then state.firstWord else state.secondWord
    flags := { state.flags with
      iteration := (if condition state then !state.flags.iteration else state.flags.iteration) } }

/-- The internally initialized Ctrl invariant gives the exact source exchange/parity action. -/
lemma step_eq_sourceStep {width : Nat} (state : Registers width)
    (preparedControl : state.control = false) : step state = sourceStep state := by
  simp only [step, preparedControl, Bool.false_xor, sourceStep]

/-- Compile precisely the same predicate, swap, parity, and inverse-predicate native list. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width enough)

/-- Exact full-register circuit realization on every encoded basis label. -/
lemma program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough) environment step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width enough) (gates_step width enough) environment

/-- The source specialization is an action of the actual native program on the prepared subspace. -/
lemma program_apply_prepared (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) (preparedControl : state.control = false) :
    (program width enough).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (sourceStep state))) := by
  rw [(program_realizes width enough).apply_encoded_ket, step_eq_sourceStep state preparedControl]

/-- Exact actual native trace, including both complete predicate passes after word movement. -/
lemma program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace =
      (conditionGates width enough).map (GateSpec.event .empty) ++
        List.replicate (3 * (width + 3)) (.gate .toffoli) ++
          [.gate .cnot] ++
            ((conditionGates width enough).map (GateSpec.event .empty)).reverse := by
  have wordTrace : (WorkWordExchange.gates width).map (GateSpec.event .empty) =
      List.replicate (3 * (width + 3)) (.gate .toffoli) := by
    simpa only [WorkWordExchange.program, GateSpec.programList_eventTrace] using
      WorkWordExchange.program_eventTrace width
  rw [program, GateSpec.programList_eventTrace]
  simp only [gates, List.map_append, List.map_reverse, wordTrace]
  rfl

/-- Both predicate passes, every actual word-swap Toffoli, and the final parity CNOT are counted. -/
lemma gates_length (width : Nat) (enough : 2 ≤ width.size) :
    (gates width enough).length = 2 * gateCount (2 * width.size - 2) + 3 * (width + 3) + 1 := by
  have predicateCount : (conditionGates width enough).length = gateCount (2 * width.size - 2) :=
    pairGates_length width .quotient .shift (by decide) enough
  have wordCount : (WorkWordExchange.gates width).length = 3 * (width + 3) := by
    have actual := congrArg List.length (WorkWordExchange.program_eventTrace width)
    simpa only [WorkWordExchange.program, GateSpec.programList_eventTrace,
      List.length_map, List.length_replicate] using actual
  have parityCount : (parityGates width).length = 1 := rfl
  simp only [gates, List.length_append, List.length_reverse, predicateCount, wordCount, parityCount]
  omega

lemma program_eventCost_card (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost.card =
      2 * gateCount (2 * width.size - 2) + 3 * (width + 3) + 1 := by
  rw [program, GateSpec.programList_eventCost_card, gates_length]

lemma program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) =
      2 * gateCount (2 * width.size - 2) + 3 * (width + 3) + 1 := by
  rw [program, GateSpec.programList_evaluatedEventDepth_unit, gates_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.BoundaryExchange
