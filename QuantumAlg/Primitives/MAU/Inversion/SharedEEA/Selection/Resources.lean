/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Schedule

/-!
# Actual finite selector ledger and independent polynomial envelope

The ordered trace below comes from the same concatenated native gate list
that implements the Sign exchange. The exact count includes every mask X,
every borrowed-work zero-test gate, the three swap Toffolis, and the full
inverse predicate. Keys with an out-of-range natural position contribute
an empty list. Unit duration depth is the strict sequential native depth.

This enumeration uses the actual baseline phase-dependent swap boundary
[LYL+26, sec_EEA/sub_regshare.tex:281-296], repairing the optimized listing's
missing phase-2 offset after moving the increment
[ibid., sub_opt.tex:52-59; NumberTheory.SharedEEA.SwapBoundary].
Its independently proved polynomial
envelope is not the paper's gate estimate. It uses only existing frame
coordinates; enumeration keys are compile-time indices, not allocated
quantum registers or observations of the quantum input.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SelectionResources

noncomputable section

open EncodedBit SelectionKey SelectionSchedule

/-- The actual ordered list of native events emitted by all finite selectors. -/
def events (width : Nat) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (keys width).flatMap fun selected =>
    (SelectionSwap.gates width selected).map (GateSpec.event .empty)

private theorem indices_events (width : Nat) (indices : List (Key width)) :
    (indices.flatMap (SelectionSwap.gates width)).map (GateSpec.event .empty) =
      indices.flatMap (fun selected =>
        (SelectionSwap.gates width selected).map (GateSpec.event .empty)) := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons]

/-- Literal event order, including both predicate passes for every valid key. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace = events width := by
  rw [program, GateSpec.programList_eventTrace]
  exact indices_events width _

/-- The strict resource pool is derived from that exact executed event list. -/
theorem program_eventCost (width : Nat) :
    (program width).eventCost = ResourcePool.ofList (events width) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_eventTrace]

/-- The depth expression retains the actual sequential dependency of every native gate. -/
theorem program_eventDepth (width : Nat) :
    (program width).eventDepth = GateSpec.depthOfEvents (events width) := by
  rw [program, GateSpec.programList_eventDepth]
  exact congrArg GateSpec.depthOfEvents (indices_events width _)

/-- Exact finite count of a key, with no gate emitted for an invalid natural index. -/
def selectorCount (width : Nat) (selected : Key width) : Nat :=
  if position selected < width + 3 then
    2 * (2 * (SelectionPredicate.maskIndices width (pattern selected)).length +
      NativePredicate.gateCount (2 * width.size)) + 3
  else 0

/-- The numerical key count is the length of its actual complete native list. -/
theorem selectorCount_eq_length (width : Nat) (selected : Key width) :
    selectorCount width selected = (SelectionSwap.gates width selected).length := by
  rw [SelectionSwap.gates_length, SelectionPredicate.gates_length]
  rfl

/-- Exact count sums the actual finite enumeration, including zero-cost skipped keys. -/
def count (width : Nat) : Nat := ((keys width).map (selectorCount width)).sum

private theorem indices_length (width : Nat) (indices : List (Key width)) :
    (indices.flatMap (SelectionSwap.gates width)).length =
      (indices.map (selectorCount width)).sum := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.map_cons, List.sum_cons,
        selectorCount_eq_length]

theorem gates_length (width : Nat) : (gates width).length = count width :=
  indices_length width _

theorem program_eventCost_card (width : Nat) :
    (program width).eventCost.card = count width := by
  rw [program, GateSpec.programList_eventCost_card, gates_length]

/-- Actual strict sequential unit depth, not a parallelized or source-assigned estimate. -/
theorem program_unitDepth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = count width := by
  rw [program, GateSpec.programList_evaluatedEventDepth_unit, gates_length]

private theorem predicate_count_le (width : Nat) (selected : Key width) :
    (SelectionPredicate.gates width (pattern selected)).length ≤ 16 * width.size + 9 := by
  rw [SelectionPredicate.gates_length]
  have masks := SelectionPredicate.maskIndices_length_le width (pattern selected)
  unfold NativePredicate.gateCount
  split_ifs <;> omega

/-- A uniform bound includes zero-width length fields and both full predicate passes. -/
theorem selectorCount_le (width : Nat) (selected : Key width) :
    selectorCount width selected ≤ 32 * width.size + 21 := by
  rw [selectorCount_eq_length, SelectionSwap.gates_length]
  have predicates := predicate_count_le width selected
  split_ifs <;> omega

private theorem indices_count_le (width : Nat) (indices : List (Key width)) :
    (indices.map (selectorCount width)).sum ≤ indices.length * (32 * width.size + 21) := by
  induction indices with
  | nil => simp
  | cons selected rest ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have current := selectorCount_le width selected
      omega

/-- Exact finite-size envelope before simplifying the actual key cardinality. -/
theorem count_le_enumeration (width : Nat) :
    count width ≤ 2 ^ (width.size + (width.size + 1)) * (32 * width.size + 21) := by
  have bounded := indices_count_le width (keys width)
  rw [keys_length] at bounded
  exact bounded

private theorem power_size_le (width : Nat) (positive : 0 < width) :
    2 ^ width.size ≤ 2 * width := by
  have sizePositive : 0 < width.size := Nat.lt_size.mpr positive
  have previous : 2 ^ (width.size - 1) ≤ width := Nat.lt_size.mp (by omega)
  calc
    2 ^ width.size = 2 ^ (width.size - 1 + 1) := congrArg (2 ^ ·) (by omega)
    _ = 2 ^ (width.size - 1) * 2 := pow_succ _ _
    _ ≤ width * 2 := Nat.mul_le_mul_right 2 previous
    _ = 2 * width := Nat.mul_comm _ _

/-- At positive modulus width, the complete actual key set has a quadratic bound. -/
theorem keys_length_le (width : Nat) (positive : 0 < width) :
    (keys width).length ≤ 8 * width ^ 2 := by
  rw [keys_length, pow_add, pow_succ]
  have powerBound := power_size_le width positive
  calc
    2 ^ width.size * (2 ^ width.size * 2) ≤ (2 * width) * ((2 * width) * 2) :=
      Nat.mul_le_mul powerBound (Nat.mul_le_mul_right 2 powerBound)
    _ = 8 * width ^ 2 := by ring

/-- Independent polynomial native count on every positive-width frame. -/
theorem count_le_polynomial (width : Nat) (positive : 0 < width) :
    count width ≤ 8 * width ^ 2 * (32 * width.size + 21) :=
  (indices_count_le width (keys width)).trans
    (Nat.mul_le_mul_right (32 * width.size + 21) (keys_length_le width positive))

/-- The original prime-modulus domain supplies positivity internally. -/
theorem prime_count_le_polynomial (modulus : Nat) (prime : modulus.Prime) :
    count modulus.size ≤ 8 * modulus.size ^ 2 * (32 * modulus.size.size + 21) :=
  count_le_polynomial modulus.size (Nat.lt_size.mpr prime.pos)

/-- Count and depth bounds refer to the same executable native program. -/
theorem program_unitDepth_le_polynomial (width : Nat) (positive : 0 < width) :
    (program width).evaluatedEventDepth (fun _ => 1) ≤
      8 * width ^ 2 * (32 * width.size + 21) := by
  rw [program_unitDepth]
  exact count_le_polynomial width positive

end

end QuantumAlg.MAU.Inversion.SharedEEA.SelectionResources
