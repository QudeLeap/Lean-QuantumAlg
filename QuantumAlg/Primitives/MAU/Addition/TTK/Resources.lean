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

private theorem pre_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((preXorGates n).map fun gate => w gate.event).sum =
      (n - 1) * w (.gate (.builtin "cnot")) := by
  simp [preXorGates, List.sum_ofFn, event]

private theorem descending_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((descendingXorGates n).map fun gate => w gate.event).sum =
      (n - 2) * w (.gate (.builtin "cnot")) := by
  simp [descendingXorGates, List.sum_ofFn, event]

private theorem carry_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((carryGates n).map fun gate => w gate.event).sum =
      (n - 1) * w (.gate (.builtin "toffoli")) := by
  simp [carryGates, List.sum_ofFn, event]

private theorem uncompute_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((descendingUncomputeGates n).map fun gate => w gate.event).sum =
      (n - 1) * (w (.gate (.builtin "cnot")) + w (.gate (.builtin "toffoli"))) := by
  simp [descendingUncomputeGates, List.sum_ofFn, event]

private theorem ascending_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((ascendingXorGates n).map fun gate => w gate.event).sum =
      (n - 2) * w (.gate (.builtin "cnot")) := by
  simpa only [ascendingXorGates, List.map_reverse, List.sum_reverse] using
    descending_weight n w

private theorem final_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((finalXorGates n).map fun gate => w gate.event).sum =
      n * w (.gate (.builtin "cnot")) := by
  simp [finalXorGates, List.sum_ofFn, event]

private theorem low_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((lowRippleGates n).map fun gate => w gate.event).sum =
      (n + 2 * (n - 1) + 2 * (n - 2)) * w (.gate (.builtin "cnot")) +
        (2 * (n - 1)) * w (.gate (.builtin "toffoli")) := by
  simp only [lowRippleGates, List.map_append, List.sum_append, pre_weight,
    descending_weight, carry_weight, uncompute_weight, ascending_weight, final_weight]
  ring

private theorem event_withOverflowGate {n : Nat}
    (gate : EncodedBit.GateSpec (encoding n)) :
    (withOverflowGate gate).event = gate.event := by
  cases gate <;> rfl

private theorem lifted_weight {n : Nat} (w : Resource.Event .quantum → Nat)
    (gates : List (EncodedBit.GateSpec (encoding n))) :
    ((gates.map withOverflowGate).map fun gate => w gate.event).sum =
      (gates.map fun gate => w gate.event).sum := by
  simp only [List.map_map, Function.comp_def, event_withOverflowGate]

private theorem overflow_weight (n : Nat) (w : Resource.Event .quantum → Nat) :
    ((overflowGates n).map fun gate => w gate.event).sum =
      (n + 2 * (n - 1) + 2 * (n - 2) + (if 2 ≤ n then 1 else 0)) *
        w (.gate (.builtin "cnot")) +
      (2 * (n - 1) + (if n = 0 then 0 else 1)) * w (.gate (.builtin "toffoli")) := by
  cases n with
  | zero => simp [overflowGates]
  | succ n =>
      cases n with
      | zero =>
          simp only [overflowGates, List.map_append, List.sum_append, lifted_weight,
            final_weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          simp [overflowCarryGate, event, Nat.add_comm]
      | succ n =>
          have hge : 2 ≤ n + 2 := by omega
          have hne : n + 2 ≠ 0 := by omega
          simp only [overflowGates, List.map_append, List.sum_append, lifted_weight,
            pre_weight, descending_weight, carry_weight, uncompute_weight,
            ascending_weight, final_weight, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, if_pos hge, if_neg hne]
          simp only [overflowPreGate, overflowCarryGate, event]
          ring

private theorem sum_map_one {α : Type} (items : List α) :
    (items.map fun _ => (1 : Nat)).sum = items.length := by
  simp

/-- Every native coordinate is determined by the actual two gate families. -/
theorem ttkLowRipple_native_count (n : Nat) (focus : Resource.Event .quantum) :
    ResourcePool.count focus (lowRippleProgram n).eventCost =
      (n + 2 * (n - 1) + 2 * (n - 2)) *
        (if (.gate (.builtin "cnot") : Resource.Event .quantum) = focus then 1 else 0) +
      (2 * (n - 1)) *
        (if (.gate (.builtin "toffoli") : Resource.Event .quantum) = focus then 1 else 0) := by
  rw [lowRippleProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact low_weight n (fun emitted => if emitted = focus then 1 else 0)

/-- Overflow uses the same native coordinates plus its actual top-bit gates. -/
theorem ttkOverflow_native_count (n : Nat) (focus : Resource.Event .quantum) :
    ResourcePool.count focus (overflowProgram n).eventCost =
      (n + 2 * (n - 1) + 2 * (n - 2) + (if 2 ≤ n then 1 else 0)) *
        (if (.gate (.builtin "cnot") : Resource.Event .quantum) = focus then 1 else 0) +
      (2 * (n - 1) + (if n = 0 then 0 else 1)) *
        (if (.gate (.builtin "toffoli") : Resource.Event .quantum) = focus then 1 else 0) := by
  rw [overflowProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact overflow_weight n (fun emitted => if emitted = focus then 1 else 0)

/-- Exact low-word CNOT count, including widths zero and one. -/
theorem ttkLowRipple_cnot_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "cnot")) (lowRippleProgram n).eventCost =
      n + 2 * (n - 1) + 2 * (n - 2) := by
  simpa [Resource.GateLabel.builtin] using
    ttkLowRipple_native_count n (.gate (.builtin "cnot"))

/-- Exact low-word Toffoli count, including empty carry sweeps. -/
theorem ttkLowRipple_toffoli_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli")) (lowRippleProgram n).eventCost =
      2 * (n - 1) := by
  simpa [Resource.GateLabel.builtin] using
    ttkLowRipple_native_count n (.gate (.builtin "toffoli"))

/-- Exact overflow CNOT count; its top CNOT is absent at widths zero and one. -/
theorem ttkOverflow_cnot_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "cnot")) (overflowProgram n).eventCost =
      n + 2 * (n - 1) + 2 * (n - 2) + (if 2 ≤ n then 1 else 0) := by
  simpa [Resource.GateLabel.builtin] using
    ttkOverflow_native_count n (.gate (.builtin "cnot"))

/-- Exact overflow Toffoli count; the top Toffoli is present at every positive width. -/
theorem ttkOverflow_toffoli_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli")) (overflowProgram n).eventCost =
      2 * (n - 1) + (if n = 0 then 0 else 1) := by
  simpa [Resource.GateLabel.builtin] using
    ttkOverflow_native_count n (.gate (.builtin "toffoli"))

private theorem low_length (n : Nat) :
    (lowRippleGates n).length = n + 4 * (n - 1) + 2 * (n - 2) := by
  have h := low_weight n (fun _ => 1)
  simp only [sum_map_one, Nat.mul_one] at h
  omega

private theorem overflow_length (n : Nat) :
    (overflowGates n).length =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  have h := overflow_weight n (fun _ => 1)
  simp only [sum_map_one, Nat.mul_one] at h
  omega

/-- The total event ledger has exactly one entry for every actual low-word gate. -/
theorem ttkLowRipple_event_count (n : Nat) :
    (lowRippleProgram n).eventCost.card = n + 4 * (n - 1) + 2 * (n - 2) := by
  rw [lowRippleProgram, programList_eventCost_card, low_length]

/-- The total overflow event count includes precisely its extra top-bit gates. -/
theorem ttkOverflow_event_count (n : Nat) :
    (overflowProgram n).eventCost.card =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  rw [overflowProgram, programList_eventCost_card, overflow_length]

/-- Unit-duration depth of the actual serial low-word list. -/
theorem ttkLowRipple_serial_depth (n : Nat) :
    (lowRippleProgram n).evaluatedEventDepth (fun _ => 1) =
      n + 4 * (n - 1) + 2 * (n - 2) := by
  rw [lowRippleProgram, programList_evaluatedEventDepth_unit, low_length]

/-- Unit-duration depth of the actual serial overflow list. -/
theorem ttkOverflow_serial_depth (n : Nat) :
    (overflowProgram n).evaluatedEventDepth (fun _ => 1) =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  rw [overflowProgram, programList_evaluatedEventDepth_unit, overflow_length]

/-- Above width one, the actual low-word circuit has `5n-6` CNOTs and `2n-2` Toffolis. -/
theorem ttkLowRipple_gate_counts_of_two_le (n : Nat) (hn : 2 ≤ n) :
    ResourcePool.count (.gate (.builtin "cnot")) (lowRippleProgram n).eventCost =
        5 * n - 6 ∧
      ResourcePool.count (.gate (.builtin "toffoli")) (lowRippleProgram n).eventCost =
        2 * n - 2 := by
  rw [ttkLowRipple_cnot_count, ttkLowRipple_toffoli_count]
  omega

/-- The overflow gate counts match the source formulas; the construction also
supports width two [TTK09, qic-loglogaddition-quant.tex:357-372]. -/
theorem ttkOverflow_gate_counts_of_two_le (n : Nat) (hn : 2 ≤ n) :
    ResourcePool.count (.gate (.builtin "cnot")) (overflowProgram n).eventCost =
        5 * n - 5 ∧
      ResourcePool.count (.gate (.builtin "toffoli")) (overflowProgram n).eventCost =
        2 * n - 1 := by
  rw [ttkOverflow_cnot_count, ttkOverflow_toffoli_count]
  have hne : n ≠ 0 := by omega
  rw [if_pos hn, if_neg hne]
  omega

/-- The serial low-word event count and depth both simplify to `7n-8`. -/
theorem ttkLowRipple_serial_resources_of_two_le (n : Nat) (hn : 2 ≤ n) :
    (lowRippleProgram n).eventCost.card = 7 * n - 8 ∧
      (lowRippleProgram n).evaluatedEventDepth (fun _ => 1) = 7 * n - 8 := by
  rw [ttkLowRipple_event_count, ttkLowRipple_serial_depth]
  omega

/-- The serial overflow event count and depth both simplify to `7n-6`. -/
theorem ttkOverflow_serial_resources_of_two_le (n : Nat) (hn : 2 ≤ n) :
    (overflowProgram n).eventCost.card = 7 * n - 6 ∧
      (overflowProgram n).evaluatedEventDepth (fun _ => 1) = 7 * n - 6 := by
  rw [ttkOverflow_event_count, ttkOverflow_serial_depth]
  have hne : n ≠ 0 := by omega
  rw [if_pos hn, if_neg hne]
  omega

/-- The actual low-word interface has two operand words and all gate wires lie in it. -/
theorem ttkLowRipple_interface (n : Nat) :
    (encoding n).width = 2 * n ∧
      (lowRippleProgram n).physical_idx ⊆ List.range (2 * n) := by
  constructor
  · exact ttkEncoding_width n
  · simpa only [lowRippleProgram, ttkEncoding_width] using
      programList_physical_idx_subset_range (lowRippleGates n)

/-- The actual overflow interface includes its output bit even when no gate touches it. -/
theorem ttkOverflow_interface (n : Nat) :
    (overflowEncoding n).width = 2 * n + 1 ∧
      (overflowProgram n).physical_idx ⊆ List.range (2 * n + 1) := by
  constructor
  · exact ttkOverflowEncoding_width n
  · simpa only [overflowProgram, ttkOverflowEncoding_width] using
      programList_physical_idx_subset_range (overflowGates n)

end

end QuantumAlg.MAU.Addition.TTK
