/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.HRS
import all QuantumAlg.Primitives.MAU.Addition.Gidney.BiFlip
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Base
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Complement
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Gates.Trace

/-!
# Exact native numerical coordinates of the existing comparison and reflection

The comparison retains its two actual HRS offsets and flag X. The large
reflection retains the complete HRS body, full target complement and real
dirty-control native lowering. These are counts of the existing unitary
source components, before the separate external EEA control lowering.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit BinaryLabelEncoding Addition.Gidney

private lemma oneDirty_pool (width : Nat) (constant : Fin (2 ^ width)) :
    ResourcePool.ofList ((Addition.HRS.oneDirtyGates width constant).map
      (GateSpec.event .empty)) = (Addition.HRS.oneDirtyProgram width constant).eventCost := by
  rw [Addition.HRS.hrsOneDirtyGates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private lemma oneDirty_source_counts (width : Nat) (constant : Fin (2 ^ width)) :
    ((Addition.HRS.oneDirtyGates width constant).map GateSpec.toffoliMultiplicity).sum =
        oneDirtyCount width constant (.gate .toffoli) ∧
      ((Addition.HRS.oneDirtyGates width constant).map GateSpec.cnotMultiplicity).sum =
        oneDirtyCount width constant (.gate .cnot) ∧
      ((Addition.HRS.oneDirtyGates width constant).map GateSpec.xMultiplicity).sum =
        oneDirtyCount width constant (.gate .singleQubit) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← GateSpec.programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, oneDirty_pool, oneDirtyCount_eq]
  · rw [← GateSpec.programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, oneDirty_pool, oneDirtyCount_eq]
  · rw [← GateSpec.programList_x_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, oneDirty_pool, oneDirtyCount_eq]

private lemma complement_events (width : Nat) :
    (complementBodyGates width).map (GateSpec.event .empty) =
      (complementGates width).map (GateSpec.event .empty) :=
  GateSpec.map_event_prodLeft (oracles := .empty) bool (complementGates width)

private lemma complement_body_counts (width : Nat) :
    ((complementBodyGates width).map GateSpec.toffoliMultiplicity).sum = 0 ∧
      ((complementBodyGates width).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((complementBodyGates width).map GateSpec.xMultiplicity).sum = width := by
  have placed := complement_events width
  refine ⟨?_, ?_, ?_⟩
  · rw [GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty placed]
    simp [complementGates, List.map_ofFn, Function.comp_def, GateSpec.toffoliMultiplicity]
  · rw [GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty placed]
    simp [complementGates, List.map_ofFn, Function.comp_def, GateSpec.cnotMultiplicity]
  · rw [GateSpec.sum_xMultiplicity_eq_of_events_eq .empty placed]
    simp [complementGates, List.map_ofFn, Function.comp_def, GateSpec.xMultiplicity]

/-- Exact native coordinates of the complete internally selected large-width reflection. -/
lemma biFlip_source_counts (width : Nat) (large : 3 ≤ width)
    (pivot : Fin (2 ^ width + 1)) :
    ((biFlipGates width pivot).map GateSpec.xMultiplicity).sum = 0 ∧
      ((biFlipGates width pivot).map GateSpec.cnotMultiplicity).sum =
        oneDirtyCount width (Addition.Gidney.negatedPivot width pivot.val)
          (.gate .singleQubit) + width ∧
      ((biFlipGates width pivot).map GateSpec.toffoliMultiplicity).sum =
        oneDirtyCount width (Addition.Gidney.negatedPivot width pivot.val) (.gate .cnot) +
          4 * oneDirtyCount width (Addition.Gidney.negatedPivot width pivot.val)
            (.gate .toffoli) := by
  have same : biFlipGates width pivot = largeBiFlipGates width large pivot := by
    rw [biFlipGates, dif_neg (by omega : ¬width ≤ 2)]
  have lowered :
      ((largeBiFlipGates width large pivot).map GateSpec.xMultiplicity).sum = 0 ∧
        ((largeBiFlipGates width large pivot).map GateSpec.cnotMultiplicity).sum =
          ((biFlipBodyGates width pivot).map GateSpec.xMultiplicity).sum ∧
        ((largeBiFlipGates width large pivot).map GateSpec.toffoliMultiplicity).sum =
          ((biFlipBodyGates width pivot).map GateSpec.cnotMultiplicity).sum +
            4 * ((biFlipBodyGates width pivot).map GateSpec.toffoliMultiplicity).sum :=
    GateSpec.controlRightList_native_counts (fun _ => boolBit) (oneDirtyBits width)
      singleBit_wire (gidneyOneDirtyBits_wire width)
      (by change 5 ≤ 1 + (width + 1); omega) boolBit (biFlipBodyGates width pivot)
  rw [same]
  simp only [biFlipBodyGates, List.map_append, List.sum_append,
    (oneDirty_source_counts width (Addition.Gidney.negatedPivot width pivot.val)).1,
    (oneDirty_source_counts width (Addition.Gidney.negatedPivot width pivot.val)).2.1,
    (oneDirty_source_counts width (Addition.Gidney.negatedPivot width pivot.val)).2.2,
    (complement_body_counts width).1, (complement_body_counts width).2.1,
    (complement_body_counts width).2.2, Nat.add_zero] at lowered
  exact lowered

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
