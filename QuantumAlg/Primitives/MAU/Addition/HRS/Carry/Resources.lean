/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry

/-!
# Literal resources of the optimized HRS carry

Each selected high constant bit contributes one CNOT and two X gates.
The first stage has either zero or one Toffoli; every subsequent stage
has two. Cleanup reverses the lower prefix, with the same native counts.
The resulting formulas concern the actual gate lists, rather than assuming
the separate source estimate [HRS16, paper.tex:195-205,245].

For input width `w >= 2`, the parameter `n = w - 2` below counts the
internal borrowed bits. The interface has `w` input bits, `n` borrowed
bits, and one output bit. Unit depth means the executed serial list.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

/-- Number of set constant bits among positions `1` through `count`. -/
def highConstantCount (constant : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => highConstantCount constant count + (constant.testBit (count + 1)).toNat

private theorem base_weight {Data : Type} {encoding : BinaryLabelEncoding Data}
    (low high output : EncodedBit encoding)
    (hlh : low.wire ≠ high.wire) (hlo : low.wire ≠ output.wire)
    (hho : high.wire ≠ output.wire) (c0 c1 : Bool)
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((baseCarryGates low high output hlh hlo hho c0 c1).map
      fun gate => weight (event .empty gate)).sum =
      c1.toNat * (weight (.gate .cnot) + 2 * weight (.gate .singleQubit)) +
        c0.toNat * weight (.gate .toffoli) := by
  cases c0 <;> cases c1
  all_goals simp [baseCarryGates, EncodedBit.GateSpec.event,
    EncodedBit.GateSpec.primitive, QubitPrimitive.event, QubitPrimitive.nativeToken,
    AlgorithmGate.model, AlgorithmGate.coordinate]
  all_goals omega

private theorem propagate_weight {Data : Type} {encoding : BinaryLabelEncoding Data}
    (input previous output : EncodedBit encoding)
    (hip : input.wire ≠ previous.wire) (hio : input.wire ≠ output.wire)
    (hpo : previous.wire ≠ output.wire) (constant : Bool)
    (lower : List (EncodedBit.GateSpec encoding))
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((propagateCarryGates input previous output hip hio hpo constant lower).map
      fun gate => weight (event .empty gate)).sum =
      (lower.map fun gate => weight (event .empty gate)).sum +
        constant.toNat *
          (weight (.gate .cnot) + 2 * weight (.gate .singleQubit)) +
        2 * weight (.gate .toffoli) := by
  cases constant
  all_goals simp [propagateCarryGates, EncodedBit.GateSpec.event,
    EncodedBit.GateSpec.primitive, QubitPrimitive.event, QubitPrimitive.nativeToken,
    AlgorithmGate.model, AlgorithmGate.coordinate]
  all_goals omega

/-- Weighted native leaves of a prefix follow from the actual local lists. -/
theorem hrsCarryPrefix_weight (width : Nat) (constant : Fin (2 ^ width))
    (index : Nat) (h : index + 2 ≤ width)
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((carryPrefix width constant index h).map fun gate => weight (event .empty gate)).sum =
      highConstantCount constant.val (index + 1) *
        (weight (.gate .cnot) + 2 * weight (.gate .singleQubit)) +
      (2 * index + (constant.val.testBit 0).toNat) * weight (.gate .toffoli) := by
  induction index with
  | zero =>
      dsimp only [carryPrefix, carryPrefixInput, carryPrefixWork]
      rw [base_weight]
      simp [highConstantCount]
  | succ index ih =>
      dsimp only [carryPrefix, carryPrefixInput, carryPrefixWork]
      rw [propagate_weight, ih]
      simp only [highConstantCount]
      ring

private theorem carry_weight (width : Nat) (constant : Fin (2 ^ width))
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((carryGates width constant).map fun gate => weight (event .empty gate)).sum =
      match width with
      | 0 => 0
      | 1 => (constant.val.testBit 0).toNat * weight (.gate .cnot)
      | n + 2 =>
          (highConstantCount constant.val (n + 1) + highConstantCount constant.val n) *
            (weight (.gate .cnot) + 2 * weight (.gate .singleQubit)) +
          (2 * n + (constant.val.testBit 0).toNat +
            (if n = 0 then 0 else 2 * (n - 1) + (constant.val.testBit 0).toNat)) *
              weight (.gate .toffoli) := by
  match width with
  | 0 => rfl
  | 1 =>
      cases hc : constant.val.testBit 0 <;>
        simp [carryGates, EncodedBit.GateSpec.event, EncodedBit.GateSpec.primitive,
          QubitPrimitive.event, QubitPrimitive.nativeToken, AlgorithmGate.model,
          AlgorithmGate.coordinate, hc]
  | n + 2 =>
      rw [carryGates, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
        hrsCarryPrefix_weight]
      cases n with
      | zero => simp [carryLowerPrefix, highConstantCount]
      | succ n =>
          rw [carryLowerPrefix, hrsCarryPrefix_weight]
          simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          ring

/-- Every coordinate of the native event pool follows from the literal list. -/
theorem hrsCarry_native_count (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (carryProgram width constant).eventCost =
      match width with
      | 0 => 0
      | 1 => (constant.val.testBit 0).toNat *
          (if (.gate .cnot : Resource.Event
            (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0)
      | n + 2 =>
          (highConstantCount constant.val (n + 1) + highConstantCount constant.val n) *
            ((if (.gate .cnot : Resource.Event
              (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0) +
              2 * (if (.gate .singleQubit : Resource.Event
                (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0)) +
          (2 * n + (constant.val.testBit 0).toNat +
            (if n = 0 then 0 else 2 * (n - 1) + (constant.val.testBit 0).toNat)) *
              (if (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model .empty)) = focus
                then 1 else 0) := by
  rw [carryProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact carry_weight width constant (fun emitted => if emitted = focus then 1 else 0)

/-- For input width `n+2`, the two selected-bit sums count the forward and
reversed lower prefixes. -/
theorem hrsCarry_cnot_count (n : Nat) (constant : Fin (2 ^ (n + 2))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (carryProgram (n + 2) constant).eventCost =
      highConstantCount constant.val (n + 1) + highConstantCount constant.val n := by
  simpa using
    hrsCarry_native_count (n + 2) constant (.gate .cnot)

/-- Each selected high constant bit adds exactly two actual X gates. -/
theorem hrsCarry_x_count (n : Nat) (constant : Fin (2 ^ (n + 2))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (carryProgram (n + 2) constant).eventCost =
      2 * (highConstantCount constant.val (n + 1) + highConstantCount constant.val n) := by
  simpa [Nat.mul_comm] using
    hrsCarry_native_count (n + 2) constant (.gate .singleQubit)

/-- The optimized first stage is counted once at width two and twice when
its inverse also appears in the cleanup. -/
theorem hrsCarry_toffoli_count (n : Nat) (constant : Fin (2 ^ (n + 2))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (carryProgram (n + 2) constant).eventCost =
      2 * n + (constant.val.testBit 0).toNat +
        (if n = 0 then 0 else 2 * (n - 1) + (constant.val.testBit 0).toNat) := by
  simpa using
    hrsCarry_native_count (n + 2) constant (.gate .toffoli)

/-- Total occurrences in the executed list, with explicit small-width cases. -/
theorem hrsCarry_event_count (width : Nat) (constant : Fin (2 ^ width)) :
    (carryProgram width constant).eventCost.card =
      match width with
      | 0 => 0
      | 1 => (constant.val.testBit 0).toNat
      | n + 2 =>
          3 * (highConstantCount constant.val (n + 1) + highConstantCount constant.val n) +
            2 * n + (constant.val.testBit 0).toNat +
              (if n = 0 then 0 else 2 * (n - 1) + (constant.val.testBit 0).toNat) := by
  rw [carryProgram, programList_eventCost_card]
  have h := carry_weight width constant (fun _ => 1)
  have hone : ((carryGates width constant).map fun _ => (1 : Nat)).sum =
      (carryGates width constant).length := by simp
  rw [hone] at h
  match width with
  | 0 => exact h
  | 1 => simpa using h
  | n + 2 => rw [h]; ring

/-- Unit-duration depth equals the actual serial event count. -/
theorem hrsCarry_serial_depth (width : Nat) (constant : Fin (2 ^ width)) :
    (carryProgram width constant).evaluatedEventDepth (fun _ => 1) =
      (carryProgram width constant).eventCost.card := by
  rw [carryProgram, programList_evaluatedEventDepth_unit, programList_eventCost_card]

/-- Width zero emits no gates; width one emits exactly its selected CNOT. -/
theorem hrsCarry_small_resources :
    (∀ constant : Fin (2 ^ 0), (carryProgram 0 constant).eventCost.card = 0) ∧
      (∀ constant : Fin (2 ^ 1), (carryProgram 1 constant).eventCost.card =
        (constant.val.testBit 0).toNat) := by
  constructor
  · intro constant
    exact hrsCarry_event_count 0 constant
  · intro constant
    exact hrsCarry_event_count 1 constant

end

end QuantumAlg.MAU.Addition.HRS
