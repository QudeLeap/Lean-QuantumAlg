/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty
import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.RecurrenceBound
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Base
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Resources of the actual one-dirty HRS constant adder

Every recurrence below is proved from `oneDirtyProgram`. The bridge uses
the actual previously verified native lowering, including its literal
four-Toffoli controlled-gate expansion. No source-paper gate constant is
substituted for that implementation [HRS16, paper.tex:219-226,245].
The exact recurrences give the explicit upper bound
`width * (39 * clog 2 width + 1)` on total events and unit-duration serial
depth, with the zero and one-width bases included.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

private lemma base_native_count (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (oneDirtyBaseProgram width constant).eventCost =
      (EncodedBit.Word.constantOneIndices constant).length *
        (if (.gate .singleQubit : Resource.Event
          (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0) := by
  rw [oneDirtyBaseProgram, programList_event_count_eq_sum_eventMultiplicity]
  by_cases h : (.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model .empty)) = focus
  · simp [oneDirtyBaseGates, EncodedBit.Word.xorConstantGates,
      Function.comp_def, eventMultiplicity, event, primitive,
      QubitPrimitive.event, QubitPrimitive.nativeToken, h]
  · simp [oneDirtyBaseGates, EncodedBit.Word.xorConstantGates,
      Function.comp_def, eventMultiplicity, event, primitive,
      QubitPrimitive.event, QubitPrimitive.nativeToken, h]

/-- Exact native-event ledger recurrence of the executed recursive program. -/
lemma hrsOneDirty_eventCost (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).eventCost =
      if width ≤ 1 then (oneDirtyBaseProgram width constant).eventCost
      else (recursiveBridgeProgram width ((splitWord width) constant).1).eventCost +
        (oneDirtyProgram (lowWidth width) ((splitWord width) constant).1).eventCost +
        (oneDirtyProgram (highWidth width) ((splitWord width) constant).2).eventCost := by
  by_cases hbase : width ≤ 1
  · conv_lhs => rw [oneDirtyProgram]
    rw [dif_pos hbase, if_pos hbase]
  · conv_lhs => rw [oneDirtyProgram]
    rw [dif_neg hbase, if_neg hbase]
    exact hrsRecursiveStep_eventCost width constant _ _

/-- Every native gate coordinate follows the same actual-program recurrence. -/
lemma hrsOneDirty_native_count (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (oneDirtyProgram width constant).eventCost =
      if width ≤ 1 then (EncodedBit.Word.constantOneIndices constant).length *
        (if (.gate .singleQubit : Resource.Event
          (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0)
      else ResourcePool.count focus
          (recursiveBridgeProgram width ((splitWord width) constant).1).eventCost +
        ResourcePool.count focus
          (oneDirtyProgram (lowWidth width) ((splitWord width) constant).1).eventCost +
        ResourcePool.count focus
          (oneDirtyProgram (highWidth width) ((splitWord width) constant).2).eventCost := by
  rw [hrsOneDirty_eventCost]
  by_cases hbase : width ≤ 1
  · simp only [if_pos hbase]
    exact base_native_count width constant focus
  · simp only [if_neg hbase]
    rw [ResourcePool.count_add, ResourcePool.count_add]

/-- Exact event count, retaining dependence on every compile-time constant half. -/
lemma hrsOneDirty_event_count (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).eventCost.card =
      if width ≤ 1 then (EncodedBit.Word.constantOneIndices constant).length
      else (recursiveBridgeProgram width ((splitWord width) constant).1).eventCost.card +
        (oneDirtyProgram (lowWidth width) ((splitWord width) constant).1).eventCost.card +
        (oneDirtyProgram (highWidth width) ((splitWord width) constant).2).eventCost.card := by
  rw [hrsOneDirty_eventCost]
  split_ifs
  · exact (hrsOneDirtyBase_resources width constant).1
  · simp only [Multiset.card_add]

/-- Evaluated event depth of the same executed three-stage recursion. -/
lemma hrsOneDirty_depth (width : Nat) (constant : Fin (2 ^ width))
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (oneDirtyProgram width constant).evaluatedEventDepth assign =
      if width ≤ 1 then (oneDirtyBaseProgram width constant).evaluatedEventDepth assign
      else (recursiveBridgeProgram width
          ((splitWord width) constant).1).evaluatedEventDepth assign +
        (oneDirtyProgram (lowWidth width)
          ((splitWord width) constant).1).evaluatedEventDepth assign +
        (oneDirtyProgram (highWidth width)
          ((splitWord width) constant).2).evaluatedEventDepth assign := by
  by_cases hbase : width ≤ 1
  · conv_lhs => rw [oneDirtyProgram]
    rw [dif_pos hbase, if_pos hbase]
  · conv_lhs => rw [oneDirtyProgram]
    rw [dif_neg hbase, if_neg hbase]
    exact hrsRecursiveStep_depth width constant _ _ assign

/-- Every nontrivial tensor factor is sequential here, so unit depth equals actual events. -/
lemma hrsOneDirty_depth_eq_events (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).evaluatedEventDepth (fun _ => 1) =
      (oneDirtyProgram width constant).eventCost.card := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
      rw [hrsOneDirty_depth, hrsOneDirty_event_count]
      split_ifs with hbase
      · exact (hrsOneDirtyBase_resources width constant).2
      · have hdecrease := hrsSplit_decreases width (by omega)
        rw [hrsRecursiveBridge_depth_eq_events,
          ih (lowWidth width) hdecrease.1 ((splitWord width) constant).1,
          ih (highWidth width) hdecrease.2 ((splitWord width) constant).2]

/-- The numerical recurrence bound is instantiated with this actual circuit's event count. -/
lemma hrsOneDirty_event_count_bound (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).eventCost.card ≤ width * (39 * Nat.clog 2 width + 1) := by
  apply hrsBalancedRecurrence_bound
    (fun width constant => (oneDirtyProgram width constant).eventCost.card)
  · intro width hbase constant
    rw [hrsOneDirty_event_count, if_pos hbase]
    exact EncodedBit.Word.constantOneIndices_length_le constant
  · intro width htwo constant
    have hbase : ¬ width ≤ 1 := by omega
    rw [hrsOneDirty_event_count, if_neg hbase]
    have hbridge := hrsRecursiveBridge_event_count_le width ((splitWord width) constant).1
    omega

/-- The same explicit logarithmic bound applies to the actual serial unit depth. -/
lemma hrsOneDirty_depth_bound (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).evaluatedEventDepth (fun _ => 1) ≤
      width * (39 * Nat.clog 2 width + 1) := by
  rw [hrsOneDirty_depth_eq_events]
  exact hrsOneDirty_event_count_bound width constant

end

end QuantumAlg.MAU.Addition.HRS
