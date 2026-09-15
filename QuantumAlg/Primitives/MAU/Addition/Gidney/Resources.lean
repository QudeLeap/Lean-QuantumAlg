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
control retains every native event coordinate and serializes the shared
control wire. The numerical envelopes below are independent of circuit
execution and use the proved HRS bound. They include all widths and pivots.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open Nat.FixedWidth

/-- One HRS negative offset followed by one X on each target bit. -/
def biFlipEventBound (width : Nat) : Nat := constantOffsetEventBound width + width

/-- Two actual controlled bi-flips and two actual comparisons. -/
def pivotEventBound (width : Nat) : Nat :=
  2 * biFlipEventBound width + 2 * comparisonEventBound width

/-- Three pivot reflections with a common target and the same two borrowed bits. -/
def modularOffsetEventBound (width : Nat) : Nat := 3 * pivotEventBound width

theorem gidneyComplement_event_count (width : Nat) :
    (complementProgram width).eventCost.card = width := by
  rw [gidneyComplement_eventCost]
  simp [ResourcePool.ofList]

/-- Adding a coherent control changes native coordinates, not the number of occurrences. -/
theorem gidneyBiFlip_event_count (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).eventCost.card =
      (HRS.oneDirtyProgram width (negatedPivot width pivot.val)).eventCost.card + width := by
  rw [gidneyBiFlip_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions,
    Multiset.card_map, Multiset.card_add, gidneyComplement_event_count]

/-- The shared coherent control forces the native body occurrences to execute serially. -/
theorem gidneyBiFlip_depth_eq_events (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).evaluatedEventDepth (fun _ => 1) =
      (biFlipProgram width pivot).eventCost.card := by
  rw [gidneyBiFlip_event_count]
  calc
    _ = DepthExpr.costEval (fun _ => (1 : Nat))
        (UnitaryCircuit.shiftPhysicalIdx 1 (biFlipBodyProgram width pivot)).eventDepth :=
      UnitaryCircuit.evaluatedEventDepth_controlQubitsAt (n := width + 1)
        (fun _ => 1) [0] (UnitaryCircuit.shiftPhysicalIdx 1 (biFlipBodyProgram width pivot))
        (UnitaryCircuit.leadingControlLayout (biFlipBodyProgram width pivot)) (1 : Fin 2)
    _ = (biFlipBodyProgram width pivot).resourcesFromEventDepth.card := by
      rw [UnitaryCircuit.shiftPhysicalIdx_eventDepth]
      exact DepthExpr.unitCost_eq_eventPool_card _
    _ = _ := by
      rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, gidneyBiFlipBody_eventCost,
        Multiset.card_add, gidneyComplement_event_count]

theorem gidneyBiFlip_event_count_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).eventCost.card ≤ biFlipEventBound width := by
  rw [gidneyBiFlip_event_count]
  exact Nat.add_le_add_right
    (HRS.hrsOneDirty_event_count_bound width (negatedPivot width pivot.val)) width

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
  rw [gidneyPivot_event_count]
  simp only [pivotProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    gidneyBiFlip_depth_eq_events, gidneyComparison_depth_eq_events]
  omega

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
  rw [gidneyModularOffset_event_count]
  simp only [modularOffsetProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    gidneyPivot_depth_eq_events]

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
        12 * (width * (39 * Nat.clog 2 width + 1)) + 6 * width + 6 := by
  unfold modularOffsetEventBound pivotEventBound biFlipEventBound
    comparisonEventBound constantOffsetEventBound
  ring

/-- The actual carrier and physical footprint contain the word and exactly two borrowed bits. -/
theorem gidneyModularOffset_qubit_count (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (encoding width).width = width + 2 ∧
      (modularOffsetProgram width modulus constant).physical_idx.length = width + 2 := by
  constructor
  · change 1 + (width + 1) = width + 2
    omega
  · rw [gidneyModularOffset_physical, List.length_range]

end

end QuantumAlg.MAU.Addition.Gidney
