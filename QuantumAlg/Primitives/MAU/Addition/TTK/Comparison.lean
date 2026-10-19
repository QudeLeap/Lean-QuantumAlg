/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction

/-!
# Non-destructive fixed-width comparison from TTK subtraction

The actual inverse overflow list writes the borrow; the lifted low-word adder
then restores both inputs. The flag is an xor-output for arbitrary initial
`z`. An unknown `z xor predicate` must not be used as if it were the predicate
alone. The flag is part of the output interface, not a restored borrowed bit.
The exact basis action introduces no relative-phase relaxation
[HRS16, paper.tex:217-225,267-287; TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec

/-- Preserve both input words and xor `right < left` into the explicit output. -/
def comparisonOutput {n : Nat} (s : OverflowRegisters n) : OverflowRegisters n :=
  (s.1, s.2 ^^ decide (s.1.2.val < s.1.1.val))

/-- Compute the borrow and restore the two operands using actual TTK gate lists. -/
def comparisonGates (n : Nat) : List (EncodedBit.GateSpec (overflowEncoding n)) :=
  overflowSubtractionGates n ++ (lowRippleGates n).map withOverflowGate

/-- Compile comparison on exactly two operand words and one xor-output bit. -/
def comparisonProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (overflowEncoding n).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (comparisonGates n)

/-- The literal gate list preserves both inputs and computes xor-output comparison. -/
lemma ttkComparison_step (n : Nat) (s : OverflowRegisters n) :
    stepList (comparisonGates n) s = comparisonOutput s := by
  have hrestore := stepList_reverse_stepList (subtractionGates n) s.1
  rw [ttkSubtraction_step n s.1] at hrestore
  simp only [subtractionGates, List.reverse_reverse] at hrestore
  rw [comparisonGates, stepList_append, ttkOverflowSubtraction_step,
    ttkWithOverflowGateList_step]
  change (stepList (lowRippleGates n) (subtractionOutput s.1),
    s.2 ^^ decide (s.1.2.val < s.1.1.val)) =
      (s.1, s.2 ^^ decide (s.1.2.val < s.1.1.val))
  rw [hrestore]

/-- Exact comparison for all widths and arbitrary initial output bits. -/
lemma ttkComparison_realizes (n : Nat) :
    UnitaryCircuit.Realizes (overflowEncoding n) (comparisonProgram n) environment
      comparisonOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (comparisonGates n) (ttkComparison_step n) environment

private lemma lifted_events {n : Nat}
    (gates : List (EncodedBit.GateSpec (encoding n))) :
    (gates.map withOverflowGate).map (event .empty) = gates.map (event .empty) := by
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext gate
  cases gate <;> rfl

/-- Native coordinates come from one inverse overflow and one forward low-word list. -/
lemma ttkComparison_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (comparisonProgram n).eventCost =
      ResourcePool.count focus (overflowProgram n).eventCost +
        ResourcePool.count focus (lowRippleProgram n).eventCost := by
  rw [comparisonProgram, comparisonGates,
    programList_event_count_eq_sum_eventMultiplicity, List.map_append, List.sum_append]
  rw [sum_eventMultiplicity_eq_of_events_eq .empty focus
    (lifted_events (lowRippleGates n))]
  rw [← programList_event_count_eq_sum_eventMultiplicity
      (layout := QubitLayout.canonical _) (oracles := .empty) focus
      (overflowSubtractionGates n),
    ← programList_event_count_eq_sum_eventMultiplicity
      (layout := QubitLayout.canonical _) (oracles := .empty) focus
      (lowRippleGates n)]
  change ResourcePool.count focus (overflowSubtractionProgram n).eventCost +
      ResourcePool.count focus (lowRippleProgram n).eventCost = _
  rw [ttkOverflowSubtraction_native_count]

/-- Exact CNOT count, including the empty and one-bit comparisons. -/
lemma ttkComparison_cnot_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (comparisonProgram n).eventCost =
      2 * (n + 2 * (n - 1) + 2 * (n - 2)) + (if 2 ≤ n then 1 else 0) := by
  rw [ttkComparison_native_count, ttkOverflow_cnot_count, ttkLowRipple_cnot_count]
  omega

/-- Exact Toffoli count for the actual comparison program. -/
lemma ttkComparison_toffoli_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (comparisonProgram n).eventCost =
      4 * (n - 1) + (if n = 0 then 0 else 1) := by
  rw [ttkComparison_native_count, ttkOverflow_toffoli_count, ttkLowRipple_toffoli_count]
  omega

/-- The actual event ledger has one occurrence for every gate in both lists. -/
lemma ttkComparison_event_count (n : Nat) :
    (comparisonProgram n).eventCost.card =
      2 * n + 8 * (n - 1) + 4 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  have h : (comparisonProgram n).eventCost.card =
      (overflowProgram n).eventCost.card + (lowRippleProgram n).eventCost.card := by
    simp only [comparisonProgram, comparisonGates, overflowSubtractionGates,
      overflowProgram, lowRippleProgram, programList_eventCost_card,
      List.length_append, List.length_reverse, List.length_map]
  rw [h, ttkOverflow_event_count, ttkLowRipple_event_count]
  omega

/-- Unit-duration serial depth of the literal comparison program. -/
lemma ttkComparison_serial_depth (n : Nat) :
    (comparisonProgram n).evaluatedEventDepth (fun _ => 1) =
      2 * n + 8 * (n - 1) + 4 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  calc
    (comparisonProgram n).evaluatedEventDepth (fun _ => 1) =
        (comparisonProgram n).eventCost.card := by
          simp only [comparisonProgram, programList_evaluatedEventDepth_unit,
            programList_eventCost_card]
    _ = _ := ttkComparison_event_count n

/-- Closed resource formulas for the actual serial composition above width one. -/
lemma ttkComparison_resources_of_two_le (n : Nat) (hn : 2 ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (comparisonProgram n).eventCost =
        10 * n - 11 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (comparisonProgram n).eventCost =
        4 * n - 3 ∧
      (comparisonProgram n).eventCost.card = 14 * n - 14 ∧
      (comparisonProgram n).evaluatedEventDepth (fun _ => 1) = 14 * n - 14 := by
  rw [ttkComparison_cnot_count, ttkComparison_toffoli_count,
    ttkComparison_event_count, ttkComparison_serial_depth]
  have hne : n ≠ 0 := by omega
  simp only [if_pos hn, if_neg hne]
  omega

/-- The real interface has two words and its output bit, with no carry workspace. -/
lemma ttkComparison_interface (n : Nat) :
    (overflowEncoding n).width = 2 * n + 1 ∧
      (QubitLayout.canonical (overflowEncoding n).width).systemIdx =
        List.range (2 * n + 1) :=
  ttkOverflow_interface n

end

end QuantumAlg.MAU.Addition.TTK
