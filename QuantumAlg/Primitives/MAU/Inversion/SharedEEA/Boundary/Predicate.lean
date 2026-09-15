/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Predicate.Read

/-!
# Actual complete-clock boundary predicate on the original shared frame

The source boundary follows the phase update and exchanges both complete
words when quotient length and shift vanish
[LYL+26, sec_EEA/sub_opt.tex:74-84]. The repaired finite-counter boundary
additionally tests the two actual high-clock positions when divisor length
is zero. Three real zero-pattern lists compute this Boolean choice into
original Ctrl. Their complete-frame action restores both arbitrary Work2
and arbitrary Iter; the source high positions need not be zero on active
inputs. No extra system is allocated for the test or its inverse.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.BoundaryPredicate

noncomputable section

open EncodedBit NativePredicate

/-- Actual quotient-zero and low-or-complete-clock boundary condition. -/
def condition {width : Nat} (state : Registers width) : Bool :=
  decide (state.quotientLength = 0 ∧ state.shift = 0 ∧
    (state.divisorLength ≠ 0 ∨ NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0))

/-- During active execution every value of the reused high positions is admitted. -/
theorem condition_active {width : Nat} (state : Registers width)
    (active : state.divisorLength ≠ 0) :
    condition state = decide (state.quotientLength = 0 ∧ state.shift = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [condition, decide_eq_true_eq]
  exact ⟨fun selected => ⟨selected.1, selected.2.1⟩,
    fun selected => ⟨selected.1, selected.2, Or.inl active⟩⟩

/-- After termination the actual boundary observes the complete retained finite clock. -/
theorem condition_terminal {width : Nat} (state : Registers width)
    (finished : state.divisorLength = 0) :
    condition state = decide (state.quotientLength = 0 ∧ state.shift = 0 ∧
      NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0) := by
  simp [condition, finished]

/-- Ctrl is disjoint from every source of its actual boundary computation. -/
theorem condition_xorControl {width : Nat} (value : Bool) (state : Registers width) :
    condition (xorControl value state) = condition state := rfl

/-- Each larger conjunction uses its real source coordinates and original restored Iter. -/
def regionGates (width : Nat) (withHigh : Bool) : List (GateSpec (encoding width)) :=
  (BoundaryPredicateLayout.layout width withHigh).patternGates (fun _ => false)

/-- Complete all-input action of the actual three-field or four-region zero pattern. -/
theorem regionGates_step (width : Nat) (withHigh : Bool) (state : Registers width) :
    GateSpec.stepList (regionGates width withHigh) state =
      xorControl (decide (state.quotientLength = 0 ∧ state.shift = 0 ∧
        state.divisorLength = 0 ∧
          (withHigh = true → NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0)))
        state := by
  rw [regionGates, Word.OneDirtyLayout.patternGates_step]
  simp only [BoundaryPredicateRead.source_zero_iff]
  exact NativePredicate.conditional_flip_xor _ state

private theorem xorControl_comp {width : Nat} (first second : Bool) (state : Registers width) :
    xorControl second (xorControl first state) = xorControl (first ^^ second) state := by
  change { state with control := (state.control ^^ first) ^^ second } =
    { state with control := state.control ^^ (first ^^ second) }
  rw [Bool.xor_assoc]

/-- The actual XOR terms are QL, QLD, and QLDH, in that emitted order. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  pairGates width .quotient .shift (by decide) enough ++
    regionGates width false ++ regionGates width true

/-- Exactly Ctrl changes; every source and arbitrary work coordinate is restored. -/
theorem gates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough) state = xorControl (condition state) state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append,
    pairGates_step, regionGates_step, regionGates_step]
  change xorControl (decide (state.quotientLength = 0 ∧ state.shift = 0 ∧
      state.divisorLength = 0 ∧ (true = true →
        NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0)))
    (xorControl (decide (state.quotientLength = 0 ∧ state.shift = 0 ∧
      state.divisorLength = 0 ∧ (false = true →
        NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0)))
      (xorControl (decide (state.quotientLength = 0 ∧ state.shift = 0)) state)) = _
  rw [xorControl_comp, xorControl_comp]
  have selected :
      ((decide (state.quotientLength = 0 ∧ state.shift = 0) ^^
        decide (state.quotientLength = 0 ∧ state.shift = 0 ∧ state.divisorLength = 0 ∧
          (false = true → NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0))) ^^
        decide (state.quotientLength = 0 ∧ state.shift = 0 ∧ state.divisorLength = 0 ∧
          (true = true → NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0))) =
        condition state := by
    by_cases quotient : state.quotientLength = (0#width.size) <;>
      by_cases low : state.shift = (0#width.size) <;>
      by_cases divisor : state.divisorLength = (0#width.size) <;>
      by_cases high : NumberTheory.SharedEEA.PaddingClock.high state.firstWord = (0#2) <;>
      simp [condition, quotient, low, divisor, high]
  rw [← Bool.xor_assoc, selected]

/-- The actual reversed computation again toggles only Ctrl and restores arbitrary work. -/
theorem reverse_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough).reverse state = xorControl (condition state) state := by
  let toggled := xorControl (condition state) state
  have forward : GateSpec.stepList (gates width enough) toggled = state := by
    rw [gates_step]
    change xorControl (condition (xorControl (condition state) state))
      (xorControl (condition state) state) = state
    rw [condition_xorControl, xorControl_twice]
  calc
    _ = GateSpec.stepList (gates width enough).reverse
        (GateSpec.stepList (gates width enough) toggled) :=
      congrArg (GateSpec.stepList (gates width enough).reverse) forward.symm
    _ = toggled := GateSpec.stepList_reverse_stepList (gates width enough) toggled

/-- Compile the same literal native predicate without a separate gate declaration. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  GateSpec.programList (gates width enough)

/-- Exact whole-frame basis action also fixes every relative amplitude. -/
theorem program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough)
      (fun state => xorControl (condition state) state) :=
  GateSpec.realizesList_congrStep _ (gates_step width enough)

/-- Every real zero-pattern gate appears in the actual predicate trace. -/
theorem program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace = (gates width enough).map GateSpec.event :=
  GateSpec.programList_eventTrace _

/-- The actual new patterns include both negative-source mask passes. -/
theorem regionGates_length_le (width : Nat) (withHigh : Bool) :
    (regionGates width withHigh).length ≤
      10 * BoundaryPredicateLayout.sourceCount width withHigh + 1 :=
  (BoundaryPredicateLayout.layout width withHigh).patternGates_length_le (fun _ => false)

/-- Literal length includes every old joint-zero gate and both new complete patterns. -/
theorem gates_length (width : Nat) (enough : 2 ≤ width.size) :
    (gates width enough).length = gateCount (2 * width.size - 2) +
      (regionGates width false).length + (regionGates width true).length := by
  simp only [gates, List.length_append, pairGates_length]

/-- Unit duration counts the actual emitted list on every quantum input. -/
theorem program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) = (gates width enough).length :=
  GateSpec.programList_evaluatedEventDepth_unit _

end

end QuantumAlg.MAU.Inversion.SharedEEA.BoundaryPredicate
