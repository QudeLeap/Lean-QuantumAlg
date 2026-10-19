/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Predicate.Layout

/-!
# Actual low-or-complete shift predicate with no new work register

The source phase-zero test follows its quotient/divisor phase update
[LYL+26, sec_EEA/sub_opt.tex:74-79]. Its terminal repair reads low shift
while the actual divisor length is nonzero, and both original high bits
and low shift when that length is zero. Three actual zero conjunctions
compute this Boolean choice into original Ctrl by XOR. The high bits
are arbitrary throughout active execution.

The original dirty-zero lists restore Work2, and the longer one-dirty
pattern restores Iter. The complete native action below changes only
Ctrl for every input frame, preserving all relative amplitudes. Both
passes' elementary gates remain present when this predicate is used in
compute/use/uncompute; it is not a classical arithmetic callback or an
unaccounted selection operation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalPredicate

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit NativePredicate

/-- Actual low zero during active execution, and actual complete-clock zero after termination. -/
def condition {width : Nat} (state : Registers width) : Bool :=
  decide (state.shift = 0 ∧ (state.divisorLength ≠ 0 ∨
    NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0))

/-- Every original high-bit value is allowed while the actual divisor length is nonzero. -/
lemma condition_active {width : Nat} (state : Registers width)
    (active : state.divisorLength ≠ 0) : condition state = decide (state.shift = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [condition, decide_eq_true_eq]
  exact ⟨And.left, fun low => ⟨low, Or.inl active⟩⟩

/-- Terminal selection reads both physical high bits and the original low field together. -/
lemma condition_terminal {width : Nat} (state : Registers width)
    (finished : state.divisorLength = 0) :
    condition state = decide (state.shift = 0 ∧
      NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0) := by
  simp [condition, finished]

/-- Writing Ctrl changes none of the actual condition's quantum source coordinates. -/
lemma condition_xorControl {width : Nat} (value : Bool) (state : Registers width) :
    condition (xorControl value state) = condition state := rfl

/-- The real high/low/divisor pattern, with the existing arbitrary Iter bit restored. -/
def clockDivisorGates (width : Nat) : List (GateSpec (encoding width)) :=
  (TerminalPredicateLayout.layout width).patternGates (fun _ => false)

/-- Complete native action of the longer conjunction on the actual original wires. -/
lemma clockDivisorGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (clockDivisorGates width) state =
      xorControl (decide
        ((NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0) ∧
          state.divisorLength = 0)) state := by
  rw [clockDivisorGates, Word.OneDirtyLayout.patternGates_step]
  simp only [TerminalPredicateLayout.source_zero_iff]
  exact NativePredicate.conditional_flip_xor _ state

private lemma xorControl_comp {width : Nat} (first second : Bool) (state : Registers width) :
    xorControl second (xorControl first state) = xorControl (first ^^ second) state := by
  change { state with control := (state.control ^^ first) ^^ second } =
    { state with control := state.control ^^ (first ^^ second) }
  rw [Bool.xor_assoc]

/-- Three actual conjunction lists implement the arithmetic XOR decomposition of the guard. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  singleGates width .shift enough ++ pairGates width .shift .divisor (by decide) enough ++
    clockDivisorGates width

/-- The actual source-dependent choice changes exactly Ctrl and restores every original field. -/
lemma gates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough) state = xorControl (condition state) state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append,
    singleGates_step, pairGates_step, clockDivisorGates_step]
  change xorControl (decide
      ((NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0) ∧
        state.divisorLength = 0))
    (xorControl (decide (state.shift = 0 ∧ state.divisorLength = 0))
      (xorControl (decide (state.shift = 0)) state)) = _
  rw [xorControl_comp, xorControl_comp]
  have selected :
      ((decide (state.shift = 0) ^^ decide (state.shift = 0 ∧ state.divisorLength = 0)) ^^
        decide ((NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0) ∧
          state.divisorLength = 0)) = condition state := by
    by_cases low : state.shift = (0#width.size) <;>
      by_cases divisor : state.divisorLength = (0#width.size) <;>
      by_cases high : NumberTheory.SharedEEA.PaddingClock.high state.firstWord = (0#2) <;>
      simp [condition, low, divisor, high]
  rw [← Bool.xor_assoc, selected]

/-- The exact inverse predicate pass again xors only Ctrl, with all dirty work restored. -/
lemma reverse_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough).reverse state = xorControl (condition state) state := by
  let toggled := xorControl (condition state) state
  have forward : GateSpec.stepList (gates width enough) toggled = state := by
    rw [gates_step]
    change xorControl (condition (xorControl (condition state) state))
      (xorControl (condition state) state) = state
    rw [condition_xorControl, xorControl_twice]
  calc
    GateSpec.stepList (gates width enough).reverse state =
        GateSpec.stepList (gates width enough).reverse
          (GateSpec.stepList (gates width enough) toggled) :=
      congrArg (GateSpec.stepList (gates width enough).reverse) forward.symm
    _ = toggled := GateSpec.stepList_reverse_stepList (gates width enough) toggled

/-- The compiled native circuit is precisely the same actual three-list predicate. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width enough)

/-- Exact complete-frame ket semantics retains every coordinate and relative amplitude. -/
lemma program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough) environment
      (fun state => xorControl (condition state) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width enough) (gates_step width enough) environment

/-- Every actual elementary event of every conjunction appears in the real circuit trace. -/
lemma program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace =
      (gates width enough).map (GateSpec.event .empty) := by
  rw [program, GateSpec.programList_eventTrace]

/-- The new conjunction's actual count has a linear bound, including both source masks. -/
lemma clockDivisorGates_length_le (width : Nat) :
    (clockDivisorGates width).length ≤ 10 * TerminalPredicateLayout.sourceCount width + 1 :=
  (TerminalPredicateLayout.layout width).patternGates_length_le (fun _ => false)

/-- Actual emitted length includes both original zero lists and the complete longer predicate. -/
lemma gates_length (width : Nat) (enough : 2 ≤ width.size) :
    (gates width enough).length = gateCount (width.size - 2) +
      gateCount (2 * width.size - 2) + (clockDivisorGates width).length := by
  simp only [gates, List.length_append, singleGates_length, pairGates_length]

/-- Strict unit duration is the full actual list length, without a selector-time convention. -/
lemma program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) = (gates width enough).length :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalPredicate
