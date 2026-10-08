/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.ModularOffset
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Literal resources of the Gidney modular offset

Event cardinalities follow the actual controlled bi-flip, four-block pivot,
and three-pivot offset programs [G17, paper.tex:276-293,319-334]. Coherent
control expands into native instructions, including the gates restoring any
borrowed wire. The numerical envelopes below are independent of circuit
execution and use the proved HRS bound. They include all widths and pivots.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open Nat.FixedWidth

/-- At most four native gates per arithmetic source gate, with the fixed small bases included. -/
def biFlipEventBound (width : Nat) : Nat :=
  4 * (constantOffsetEventBound width + width) + 2

/-- Two actual controlled bi-flips and two actual comparisons. -/
def pivotEventBound (width : Nat) : Nat :=
  2 * biFlipEventBound width + 2 * comparisonEventBound width

/-- Three pivot reflections with a common target and the same two borrowed bits. -/
def modularOffsetEventBound (width : Nat) : Nat := 3 * pivotEventBound width

theorem gidneyComplement_event_count (width : Nat) :
    (complementProgram width).eventCost.card = width := by
  rw [gidneyComplement_eventCost]
  simp [ResourcePool.ofList]

/-- The native count includes every gate introduced by coherent-control expansion. -/
theorem gidneyBiFlip_event_count (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).eventCost.card = (biFlipGates width pivot).length :=
  EncodedBit.GateSpec.programList_eventCost_card _ _ _

/-- The literal list executes serially, so unit-duration depth equals its actual gate count. -/
theorem gidneyBiFlip_depth_eq_events (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).evaluatedEventDepth (fun _ => 1) =
      (biFlipProgram width pivot).eventCost.card := by
  rw [biFlipProgram, EncodedBit.GateSpec.programList_evaluatedEventDepth_unit,
    EncodedBit.GateSpec.programList_eventCost_card]

theorem gidneyBiFlip_event_count_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).eventCost.card ≤ biFlipEventBound width := by
  rw [gidneyBiFlip_event_count]
  exact gidneyBiFlipGates_length_bound width pivot

/-- Exact cardinality of the four actual blocks; the comparison keeps its zero-pivot branch. -/
theorem gidneyPivot_event_count (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width pivot).eventCost.card =
      2 * (biFlipProgram width pivot).eventCost.card +
        2 * (comparisonProgram width pivot).eventCost.card := by
  rw [gidneyPivot_eventCost]
  simp only [Multiset.card_add]
  omega

theorem gidneyPivot_depth_eq_events (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width pivot).evaluatedEventDepth (fun _ => 1) =
      (pivotProgram width pivot).eventCost.card := by
  rw [pivotProgram, EncodedBit.GateSpec.programList_evaluatedEventDepth_unit,
    EncodedBit.GateSpec.programList_eventCost_card]

theorem gidneyPivot_event_count_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width pivot).eventCost.card ≤ pivotEventBound width := by
  rw [gidneyPivot_event_count]
  have hb := gidneyBiFlip_event_count_bound width pivot
  have hc := gidneyComparison_event_count_bound width pivot
  unfold pivotEventBound
  omega

/-- The exact modular-offset count is the sum of the three executed pivot counts. -/
theorem gidneyModularOffset_event_count (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).eventCost.card =
      (pivotProgram width (offsetFirstPivot modulus constant)).eventCost.card +
        (pivotProgram width modulus).eventCost.card +
          (pivotProgram width (offsetLastPivot modulus constant)).eventCost.card := by
  rw [gidneyModularOffset_eventCost]
  simp only [Multiset.card_add]

theorem gidneyModularOffset_depth_eq_events (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).evaluatedEventDepth (fun _ => 1) =
      (modularOffsetProgram width modulus constant).eventCost.card := by
  rw [modularOffsetProgram, EncodedBit.GateSpec.programList_evaluatedEventDepth_unit,
    EncodedBit.GateSpec.programList_eventCost_card]

/-- An independent logarithmic envelope holds for every fitted modulus and constant. -/
theorem gidneyModularOffset_event_count_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).eventCost.card ≤
      modularOffsetEventBound width := by
  rw [gidneyModularOffset_event_count]
  have hfirst := gidneyPivot_event_count_bound width (offsetFirstPivot modulus constant)
  have hmiddle := gidneyPivot_event_count_bound width modulus
  have hlast := gidneyPivot_event_count_bound width (offsetLastPivot modulus constant)
  unfold modularOffsetEventBound
  omega

theorem gidneyModularOffset_depth_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).evaluatedEventDepth (fun _ => 1) ≤
      modularOffsetEventBound width := by
  rw [gidneyModularOffset_depth_eq_events]
  exact gidneyModularOffset_event_count_bound width modulus constant

/-- Expanded numerical envelope; this is an upper bound, not an optimized gate count. -/
theorem gidneyModularOffsetEventBound_expanded (width : Nat) :
    modularOffsetEventBound width =
      6 * ((1 + width) * (39 * Nat.clog 2 (1 + width) + 1)) +
        30 * (width * (39 * Nat.clog 2 width + 1)) + 24 * width + 18 := by
  unfold modularOffsetEventBound pivotEventBound biFlipEventBound
    comparisonEventBound constantOffsetEventBound
  ring

/-- The actual typed carrier contains the word and exactly two borrowed bits. -/
theorem gidneyModularOffset_qubit_count (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (encoding width).width = width + 2 ∧
      (QubitLayout.canonical (encoding width).width).systemIdx.length = width + 2 := by
  constructor
  · change 1 + (width + 1) = width + 2
    omega
  · rw [(gidneyModularOffset_interface width modulus constant).2, List.length_range]

end

end QuantumAlg.MAU.Addition.Gidney
