/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison

/-!
# Actual event and serial-depth resources of constant comparison

The nonzero-pivot construction executes one extended HRS offset, one
low-word HRS offset, and one X; pivot zero executes identity. Counts are
derived from those programs, not the source's asymptotic estimate
[G17, paper.tex:380-389]. The independent explicit upper bound reuses the
proved HRS logarithmic envelope and includes the empty target word.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

/-- Independent upper envelope for the already proved HRS offset construction. -/
def constantOffsetEventBound (width : Nat) : Nat :=
  width * (39 * Nat.clog 2 width + 1)

/-- Independent bound for one extended offset, one low offset, and the final X. -/
def comparisonEventBound (width : Nat) : Nat :=
  constantOffsetEventBound (1 + width) + constantOffsetEventBound width + 1

theorem gidneyLowOffset_eventCost (width : Nat) (constant : Fin (2 ^ width)) :
    (lowOffsetProgram width constant).eventCost =
      (HRS.oneDirtyProgram width constant).eventCost :=
  UnitaryCircuit.prodRight_eventCost (m := 1) (HRS.oneDirtyProgram width constant)

theorem gidneyLowOffset_depth (width : Nat) (constant : Fin (2 ^ width))
    (assign : Resource.Event .quantum → Nat) :
    (lowOffsetProgram width constant).evaluatedEventDepth assign =
      (HRS.oneDirtyProgram width constant).evaluatedEventDepth assign :=
  UnitaryCircuit.prodRight_evaluatedEventDepth (m := 1) assign
    (HRS.oneDirtyProgram width constant)

theorem gidneyFlagFlip_eventCost (width : Nat) :
    (flagFlipProgram width).eventCost = ResourcePool.singleton (.gate (.builtin "x")) :=
  EncodedBit.GateSpec.program_eventCost (.x (flagBit width))

theorem gidneyFlagFlip_depth (width : Nat) :
    (flagFlipProgram width).evaluatedEventDepth (fun _ => 1) = 1 := by
  change (EncodedBit.GateSpec.program (.x (flagBit width))).evaluatedEventDepth (fun _ => 1) = 1
  simp [UnitaryCircuit.evaluatedEventDepth]

/-- The exact ledger retains the two actual offset ledgers and the one final native X. -/
theorem gidneyComparison_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonProgram width pivot).eventCost =
      if pivot.val = 0 then 0 else
        (HRS.oneDirtyProgram (1 + width) (extendedNegatedPivot width pivot.val)).eventCost +
          (HRS.oneDirtyProgram width (pivotWord width pivot.val)).eventCost +
            ResourcePool.singleton (.gate (.builtin "x")) := by
  by_cases hzero : pivot.val = 0
  · simp only [comparisonProgram, if_pos hzero, identityProgram,
      UnitaryCircuit.identity_eventCost]
  · have hpacked := (gidneyPackedOffset_resources width
      (extendedNegatedPivot width pivot.val) (fun _ => 1)).1
    simp only [comparisonProgram, if_neg hzero, positiveComparisonProgram,
      UnitaryCircuit.seq_eventCost, identityProgram, UnitaryCircuit.identity_eventCost,
      add_zero, hpacked, gidneyLowOffset_eventCost, gidneyFlagFlip_eventCost]

/-- Literal event cardinality, including the independently selected zero-pivot branch. -/
theorem gidneyComparison_event_count (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonProgram width pivot).eventCost.card =
      if pivot.val = 0 then 0 else
        (HRS.oneDirtyProgram (1 + width) (extendedNegatedPivot width pivot.val)).eventCost.card +
          (HRS.oneDirtyProgram width (pivotWord width pivot.val)).eventCost.card + 1 := by
  rw [gidneyComparison_eventCost]
  split_ifs
  · rfl
  · simp only [Multiset.card_add, ResourcePool.singleton, Multiset.card_replicate]

/-- This comparison is serial: its actual unit-duration depth equals its event count. -/
theorem gidneyComparison_depth_eq_events (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonProgram width pivot).evaluatedEventDepth (fun _ => 1) =
      (comparisonProgram width pivot).eventCost.card := by
  rw [gidneyComparison_event_count]
  have hidentity : (identityProgram width).evaluatedEventDepth (fun _ => 1) = 0 := rfl
  by_cases hzero : pivot.val = 0
  · rw [if_pos hzero]
    simpa only [comparisonProgram, if_pos hzero] using hidentity
  · rw [if_neg hzero]
    have hpacked := (gidneyPackedOffset_resources width
      (extendedNegatedPivot width pivot.val) (fun _ => 1)).2
    simp only [comparisonProgram, if_neg hzero, positiveComparisonProgram,
      UnitaryCircuit.evaluatedEventDepth_seq, hidentity, Nat.add_zero,
      hpacked, gidneyLowOffset_depth, gidneyFlagFlip_depth, HRS.hrsOneDirty_depth_eq_events]

/-- The actual event count meets the independently stated logarithmic envelope. -/
theorem gidneyComparison_event_count_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonProgram width pivot).eventCost.card ≤ comparisonEventBound width := by
  rw [gidneyComparison_event_count]
  by_cases hzero : pivot.val = 0
  · rw [if_pos hzero]
    exact Nat.zero_le _
  · rw [if_neg hzero]
    have hextended := HRS.hrsOneDirty_event_count_bound (1 + width)
      (extendedNegatedPivot width pivot.val)
    have hlow := HRS.hrsOneDirty_event_count_bound width (pivotWord width pivot.val)
    unfold comparisonEventBound constantOffsetEventBound
    omega

theorem gidneyComparison_depth_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonProgram width pivot).evaluatedEventDepth (fun _ => 1) ≤
      comparisonEventBound width := by
  rw [gidneyComparison_depth_eq_events]
  exact gidneyComparison_event_count_bound width pivot

end

end QuantumAlg.MAU.Addition.Gidney
