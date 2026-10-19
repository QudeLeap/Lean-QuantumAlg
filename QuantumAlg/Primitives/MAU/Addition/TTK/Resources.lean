/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Gates
import Mathlib.Tactic.Ring

/-!
# Native resources of the literal TTK circuits

All counts below come from the actual CNOT and Toffoli lists compiled by the
programs. The all-width formulas retain truncated subtractions and the two
small overflow cases. For widths at least two, the overflow gate counts agree
with the source's formulas, which it states for widths at least three.

The evaluated depth here is the unit-duration depth of the serial gate list.
The source's smaller `5n - 3` depth parallelizes the first and last stages;
that different scheduling is not implemented by `programList`
[TTK09, qic-loglogaddition-quant.tex:357-372].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

@[simp] private lemma event_cnot {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (control target : EncodedBit encoding) (different : control.wire ≠ target.wire) :
    (EncodedBit.GateSpec.cnot control target different).event .empty =
      (Resource.Event.gate .cnot :
        Resource.Event (.quantum AlgorithmGate.model .empty)) := by
  rfl

@[simp] private lemma event_toffoli {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (EncodedBit.GateSpec.toffoli first second target firstSecond firstTarget
      secondTarget).event .empty =
      (Resource.Event.gate .toffoli :
        Resource.Event (.quantum AlgorithmGate.model .empty)) := by
  rfl

private lemma pre_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((preXorGates n).map fun gate => w (gate.event .empty)).sum =
      (n - 1) * w (.gate .cnot) := by
  simp [preXorGates, List.sum_ofFn]

private lemma descending_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((descendingXorGates n).map fun gate => w (gate.event .empty)).sum =
      (n - 2) * w (.gate .cnot) := by
  simp [descendingXorGates, List.sum_ofFn]

private lemma carry_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((carryGates n).map fun gate => w (gate.event .empty)).sum =
      (n - 1) * w (.gate .toffoli) := by
  simp [carryGates, List.sum_ofFn]

private lemma uncompute_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((descendingUncomputeGates n).map fun gate => w (gate.event .empty)).sum =
      (n - 1) * (w (.gate .cnot) + w (.gate .toffoli)) := by
  simp [descendingUncomputeGates, List.sum_ofFn]

private lemma ascending_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((ascendingXorGates n).map fun gate => w (gate.event .empty)).sum =
      (n - 2) * w (.gate .cnot) := by
  simpa only [ascendingXorGates, List.map_reverse, List.sum_reverse] using
    descending_weight n w

private lemma final_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((finalXorGates n).map fun gate => w (gate.event .empty)).sum =
      n * w (.gate .cnot) := by
  simp [finalXorGates, List.sum_ofFn]

private lemma low_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((lowRippleGates n).map fun gate => w (gate.event .empty)).sum =
      (n + 2 * (n - 1) + 2 * (n - 2)) * w (.gate .cnot) +
        (2 * (n - 1)) * w (.gate .toffoli) := by
  simp only [lowRippleGates, List.map_append, List.sum_append, pre_weight,
    descending_weight, carry_weight, uncompute_weight, ascending_weight, final_weight]
  ring

private lemma event_withOverflowGate {n : Nat}
    (gate : EncodedBit.GateSpec (encoding n)) :
    (withOverflowGate gate).event .empty = gate.event .empty := by
  cases gate <;> rfl

private lemma lifted_weight {n : Nat}
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (gates : List (EncodedBit.GateSpec (encoding n))) :
    ((gates.map withOverflowGate).map fun gate => w (gate.event .empty)).sum =
      (gates.map fun gate => w (gate.event .empty)).sum := by
  simp only [List.map_map, Function.comp_def, event_withOverflowGate]

private lemma overflow_weight (n : Nat)
    (w : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((overflowGates n).map fun gate => w (gate.event .empty)).sum =
      (n + 2 * (n - 1) + 2 * (n - 2) + (if 2 ≤ n then 1 else 0)) *
        w (.gate .cnot) +
      (2 * (n - 1) + (if n = 0 then 0 else 1)) * w (.gate .toffoli) := by
  cases n with
  | zero => simp [overflowGates]
  | succ n =>
      cases n with
      | zero =>
          simp only [overflowGates, List.map_append, List.sum_append, lifted_weight,
            final_weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          simp [overflowCarryGate, Nat.add_comm]
      | succ n =>
          have hge : 2 ≤ n + 2 := by omega
          have hne : n + 2 ≠ 0 := by omega
          simp only [overflowGates, List.map_append, List.sum_append, lifted_weight,
            pre_weight, descending_weight, carry_weight, uncompute_weight,
            ascending_weight, final_weight, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, if_pos hge, if_neg hne]
          simp only [overflowPreGate, overflowCarryGate, event_cnot, event_toffoli]
          ring

private lemma sum_map_one {α : Type} (items : List α) :
    (items.map fun _ => (1 : Nat)).sum = items.length := by
  simp

/-- Every native coordinate is determined by the actual two gate families. -/
lemma ttkLowRipple_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (lowRippleProgram n).eventCost =
      (n + 2 * (n - 1) + 2 * (n - 2)) *
        (if (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty)) =
          focus then 1 else 0) +
      (2 * (n - 1)) *
        (if (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model .empty)) =
          focus then 1 else 0) := by
  rw [lowRippleProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact low_weight n (fun emitted => if emitted = focus then 1 else 0)

/-- Overflow uses the same native coordinates plus its actual top-bit gates. -/
lemma ttkOverflow_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (overflowProgram n).eventCost =
      (n + 2 * (n - 1) + 2 * (n - 2) + (if 2 ≤ n then 1 else 0)) *
        (if (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty)) =
          focus then 1 else 0) +
      (2 * (n - 1) + (if n = 0 then 0 else 1)) *
        (if (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model .empty)) =
          focus then 1 else 0) := by
  rw [overflowProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact overflow_weight n (fun emitted => if emitted = focus then 1 else 0)

/-- Exact low-word CNOT count, including widths zero and one. -/
lemma ttkLowRipple_cnot_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (lowRippleProgram n).eventCost =
      n + 2 * (n - 1) + 2 * (n - 2) := by
  simpa using ttkLowRipple_native_count n
    (Resource.Event.gate .cnot :
      Resource.Event (.quantum AlgorithmGate.model .empty))

/-- Exact low-word Toffoli count, including empty carry sweeps. -/
lemma ttkLowRipple_toffoli_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (lowRippleProgram n).eventCost =
      2 * (n - 1) := by
  simpa using ttkLowRipple_native_count n
    (Resource.Event.gate .toffoli :
      Resource.Event (.quantum AlgorithmGate.model .empty))

/-- Exact overflow CNOT count; its top CNOT is absent at widths zero and one. -/
lemma ttkOverflow_cnot_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (overflowProgram n).eventCost =
      n + 2 * (n - 1) + 2 * (n - 2) + (if 2 ≤ n then 1 else 0) := by
  simpa using ttkOverflow_native_count n
    (Resource.Event.gate .cnot :
      Resource.Event (.quantum AlgorithmGate.model .empty))

/-- Exact overflow Toffoli count; the top Toffoli is present at every positive width. -/
lemma ttkOverflow_toffoli_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (overflowProgram n).eventCost =
      2 * (n - 1) + (if n = 0 then 0 else 1) := by
  simpa using ttkOverflow_native_count n
    (Resource.Event.gate .toffoli :
      Resource.Event (.quantum AlgorithmGate.model .empty))

private lemma low_length (n : Nat) :
    (lowRippleGates n).length = n + 4 * (n - 1) + 2 * (n - 2) := by
  have h := low_weight n (fun _ => 1)
  simp only [sum_map_one, Nat.mul_one] at h
  omega

private lemma overflow_length (n : Nat) :
    (overflowGates n).length =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  have h := overflow_weight n (fun _ => 1)
  simp only [sum_map_one, Nat.mul_one] at h
  omega

/-- The total event ledger has exactly one entry for every actual low-word gate. -/
lemma ttkLowRipple_event_count (n : Nat) :
    (lowRippleProgram n).eventCost.card = n + 4 * (n - 1) + 2 * (n - 2) := by
  rw [lowRippleProgram, programList_eventCost_card, low_length]

/-- The total overflow event count includes precisely its extra top-bit gates. -/
lemma ttkOverflow_event_count (n : Nat) :
    (overflowProgram n).eventCost.card =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  rw [overflowProgram, programList_eventCost_card, overflow_length]

/-- Unit-duration depth of the actual serial low-word list. -/
lemma ttkLowRipple_serial_depth (n : Nat) :
    (lowRippleProgram n).evaluatedEventDepth (fun _ => 1) =
      n + 4 * (n - 1) + 2 * (n - 2) := by
  rw [lowRippleProgram, programList_evaluatedEventDepth_unit, low_length]

/-- Unit-duration depth of the actual serial overflow list. -/
lemma ttkOverflow_serial_depth (n : Nat) :
    (overflowProgram n).evaluatedEventDepth (fun _ => 1) =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  rw [overflowProgram, programList_evaluatedEventDepth_unit, overflow_length]

/-- Above width one, the actual low-word circuit has `5n-6` CNOTs and `2n-2` Toffolis. -/
lemma ttkLowRipple_gate_counts_of_two_le (n : Nat) (hn : 2 ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (lowRippleProgram n).eventCost =
        5 * n - 6 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (lowRippleProgram n).eventCost =
        2 * n - 2 := by
  rw [ttkLowRipple_cnot_count, ttkLowRipple_toffoli_count]
  omega

/-- The overflow gate counts match the source formulas; the construction also
supports width two [TTK09, qic-loglogaddition-quant.tex:357-372]. -/
lemma ttkOverflow_gate_counts_of_two_le (n : Nat) (hn : 2 ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (overflowProgram n).eventCost =
        5 * n - 5 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (overflowProgram n).eventCost =
        2 * n - 1 := by
  rw [ttkOverflow_cnot_count, ttkOverflow_toffoli_count]
  have hne : n ≠ 0 := by omega
  rw [if_pos hn, if_neg hne]
  omega

/-- The serial low-word event count and depth both simplify to `7n-8`. -/
lemma ttkLowRipple_serial_resources_of_two_le (n : Nat) (hn : 2 ≤ n) :
    (lowRippleProgram n).eventCost.card = 7 * n - 8 ∧
      (lowRippleProgram n).evaluatedEventDepth (fun _ => 1) = 7 * n - 8 := by
  rw [ttkLowRipple_event_count, ttkLowRipple_serial_depth]
  omega

/-- The serial overflow event count and depth both simplify to `7n-6`. -/
lemma ttkOverflow_serial_resources_of_two_le (n : Nat) (hn : 2 ≤ n) :
    (overflowProgram n).eventCost.card = 7 * n - 6 ∧
      (overflowProgram n).evaluatedEventDepth (fun _ => 1) = 7 * n - 6 := by
  rw [ttkOverflow_event_count, ttkOverflow_serial_depth]
  have hne : n ≠ 0 := by omega
  rw [if_pos hn, if_neg hne]
  omega

/-- The actual low-word interface has two operand words and uses their canonical layout. -/
private lemma canonical_systemIdx (width : Nat) :
    (QubitLayout.canonical width).systemIdx = List.range width := by
  change List.ofFn (fun index : Fin width => index.val) = List.range width
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

/-- The actual low-word interface has two operand words and uses their canonical layout. -/
lemma ttkLowRipple_interface (n : Nat) :
    (encoding n).width = 2 * n ∧
      (QubitLayout.canonical (encoding n).width).systemIdx =
        List.range (2 * n) := by
  constructor
  · exact ttkEncoding_width n
  · rw [ttkEncoding_width]
    exact canonical_systemIdx (2 * n)

/-- The actual overflow interface includes its output bit in the canonical layout. -/
lemma ttkOverflow_interface (n : Nat) :
    (overflowEncoding n).width = 2 * n + 1 ∧
      (QubitLayout.canonical (overflowEncoding n).width).systemIdx =
        List.range (2 * n + 1) := by
  constructor
  · exact ttkOverflowEncoding_width n
  · rw [ttkOverflowEncoding_width]
    exact canonical_systemIdx (2 * n + 1)

end

end QuantumAlg.MAU.Addition.TTK
