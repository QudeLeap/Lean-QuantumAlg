/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Gates.Trace

/-! # Exact chronological comparison instructions, including the zero-pivot branch -/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open EncodedBit GateSpec BinaryLabelEncoding

/-- Complete physical packing retains the actual extended-offset instruction order. -/
lemma gidneyPackedOffsetGates_trace (width : Nat) (constant : Fin (2 ^ (1 + width))) :
    (packedOffsetGates width constant).map (event .empty) =
      (packedOffsetProgram width constant).eventTrace := by
  simp only [packedOffsetGates, List.map_map, Function.comp_def, FullPlacement.placeGate_event]
  rw [HRS.hrsOneDirtyGates_trace, packedOffsetProgram,
    UnitaryCircuit.castCanonicalQubitWidth_eventTrace]

/-- The restoring low-word offset retains every original event after the untouched flag. -/
lemma gidneyLowOffsetGates_trace (width : Nat) (constant : Fin (2 ^ width)) :
    (lowOffsetGates width constant).map (event .empty) =
      (lowOffsetProgram width constant).eventTrace := by
  erw [lowOffsetGates, map_event_prodRight, HRS.hrsOneDirtyGates_trace,
    lowOffsetProgram, UnitaryCircuit.onCanonicalBinarySuffix,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventTrace]
  rfl

/-- Zero pivot emits no instruction; every other pivot keeps both offsets and the actual flag X. -/
lemma gidneyComparisonGates_trace (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonGates width pivot).map (event .empty) =
      (comparisonProgram width pivot).eventTrace := by
  by_cases zero : pivot.val = 0
  · rw [comparisonGates, if_pos zero, comparisonProgram, if_pos zero]
    rfl
  · rw [comparisonGates, if_neg zero, comparisonProgram, if_neg zero]
    simp only [positiveComparisonGates, List.map_append, gidneyPackedOffsetGates_trace,
      gidneyLowOffsetGates_trace, positiveComparisonProgram, UnitaryCircuit.seq_eventTrace]
    rfl

end

end QuantumAlg.MAU.Addition.Gidney
