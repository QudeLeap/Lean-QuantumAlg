/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Gates

/-!
# Native computation, use, and inverse cleanup of the phase predicate

The source condition is quotient length zero and divisor length nonzero
[LYL+26, sec_EEA/sub_regshare.tex:303-305; sec_EEA/sub_opt.tex:74-76].
Its xor-output is the xor of the quotient-zero predicate and the joint
quotient/divisor-zero predicate. Both are actual elementary circuits that
restore the arbitrary incoming Work2 contents.

The same program then executes the three ordered phase Toffoli gates and
reverses the complete predicate computation. Its full-register semantics
are proved for every incoming Ctrl value, which is restored exactly.
On the internally prepared Ctrl-zero subspace the flags agree with the
source phase update. This is a local invariant to be established by the
algorithm's preparation, not an extra assumption on the eventual input.
Initialization and the other arithmetic/phase kernels remain separate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeControl

noncomputable section

open EncodedBit PredicateLayout NativePredicate NumberTheory.SharedEEA

/-- The actual retained-length condition; no precomputed quotient is supplied. -/
def condition {width : Nat} (state : Registers width) : Bool :=
  decide (state.quotientLength = 0 ∧ state.divisorLength ≠ 0)

private theorem condition_xorControl {width : Nat} (value : Bool) (state : Registers width) :
    condition (xorControl value state) = condition state := rfl

private theorem xorControl_comp {width : Nat} (first second : Bool) (state : Registers width) :
    xorControl second (xorControl first state) = xorControl (first ^^ second) state := by
  cases first <;> cases second <;> cases selected : state.control <;> simp [xorControl, selected]

/-- Compute the source condition into the existing Ctrl by two actual zero-predicate lists. -/
def conditionGates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  singleGates width .quotient enough ++ pairGates width .quotient .divisor (by decide) enough

/-- The full literal predicate computation xors exactly the retained-length condition. -/
theorem conditionGates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (conditionGates width enough) state = xorControl (condition state) state := by
  rw [conditionGates, GateSpec.stepList_append, singleGates_step, pairGates_step]
  change xorControl (decide (state.quotientLength = 0 ∧ state.divisorLength = 0))
    (xorControl (decide (state.quotientLength = 0)) state) = xorControl (condition state) state
  rw [xorControl_comp]
  have predicate : (decide (state.quotientLength = 0) ^^
      decide (state.quotientLength = 0 ∧ state.divisorLength = 0)) = condition state := by
    by_cases quotientZero : state.quotientLength = (0#width.size) <;>
      by_cases divisorZero : state.divisorLength = (0#width.size) <;>
      simp [condition, quotientZero, divisorZero]
  rw [predicate]

/-- The actual inverse gate list has the same xor action, with arbitrary work restored again. -/
theorem conditionGates_reverse_step (width : Nat) (enough : 2 ≤ width.size)
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

/-- Complete mathematical action on arbitrary Ctrl, preserving its original value. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  { state with flags :=
      if state.control ^^ condition state
      then PhaseControl.update true true false state.flags else state.flags }

private theorem condition_step {width : Nat} (state : Registers width) :
    condition (step state) = condition state := rfl

private theorem update_computed {width : Nat} (state : Registers width) :
    PhaseGates.updateStep (xorControl (condition state) state) =
      xorControl (condition state) (step state) := rfl

/-- Execute predicate computation, the ordered phase gates, and its literal inverse computation. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  conditionGates width enough ++ PhaseGates.updateGates width ++
    (conditionGates width enough).reverse

/-- Full-register correctness of the actual compute/use/inverse-cleanup sequence. -/
theorem gates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough) state = step state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append,
    conditionGates_step, PhaseGates.updateGates_step, update_computed,
    conditionGates_reverse_step, condition_xorControl, condition_step, xorControl_twice]

/-- Ctrl is restored even for inputs outside the algorithm's prepared-zero subspace. -/
theorem gates_control (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    (GateSpec.stepList (gates width enough) state).control = state.control := by
  rw [gates_step]
  rfl

/-- Therefore the internal Ctrl-zero invariant survives this actual native sequence. -/
theorem gates_control_clean (width : Nat) (enough : 2 ≤ width.size) (state : Registers width)
    (clean : state.control = false) :
    (GateSpec.stepList (gates width enough) state).control = false := by
  rw [gates_control, clean]

/-- The source's phase-update formula, with predicates computed from actual retained lengths. -/
def sourceStep {width : Nat} (state : Registers width) : Registers width :=
  { state with
    flags := (PhaseControl.update (decide (state.quotientLength = 0))
      (decide (state.divisorLength ≠ 0)) false state.flags) }

/-- On internally prepared Ctrl zero, the actual flags equal the registered source assignments. -/
theorem step_eq_sourceStep {width : Nat} (state : Registers width) (clean : state.control = false) :
    step state = sourceStep state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, flags, control⟩
  change control = false at clean
  subst control
  by_cases quotientZero : lengthQ = (0#width.size) <;>
    by_cases divisorZero : lengthR = (0#width.size) <;>
    simp [step, sourceStep, condition, PhaseControl.update, quotientZero, divisorZero]

/-- The compiled program is precisely the above native list. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width enough)

/-- Its exact all-label realization retains relative phases by the original circuit semantics. -/
theorem program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (layout := QubitLayout.canonical _)
      (encoding width) (program width enough) step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width enough)

/-- The actual program acts as the source phase update on each internally prepared basis label. -/
theorem program_apply_clean (width : Nat) (enough : 2 ≤ width.size) (state : Registers width)
    (clean : state.control = false) :
    (program width enough).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (sourceStep state))) := by
  rw [(program_realizes width enough).apply_encoded_ket, step_eq_sourceStep state clean]

/-- The independently written elementary count of one predicate computation. -/
def conditionCount (width : Nat) : Nat :=
  gateCount (width.size - 2) + gateCount (2 * width.size - 2)

theorem conditionGates_length (width : Nat) (enough : 2 ≤ width.size) :
    (conditionGates width enough).length = conditionCount width := by
  rw [conditionGates, List.length_append, singleGates_length, pairGates_length]
  rfl

/-- Both complete predicate passes and all three Toffoli gates are counted. -/
theorem gates_length (width : Nat) (enough : 2 ≤ width.size) :
    (gates width enough).length = 2 * conditionCount width + 3 := by
  have phaseCount : (PhaseGates.updateGates width).length = 3 := rfl
  simp only [gates, List.length_append, List.length_reverse, conditionGates_length, phaseCount]
  omega

theorem program_eventCost_card (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost.card = 2 * conditionCount width + 3 := by
  rw [program, GateSpec.programList_eventCost_card, gates_length]

theorem program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) = 2 * conditionCount width + 3 := by
  rw [program, GateSpec.programList_evaluatedEventDepth_unit, gates_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeControl
