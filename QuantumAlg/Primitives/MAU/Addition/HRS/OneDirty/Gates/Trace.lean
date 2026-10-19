/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Gates

/-! # Exact ordered native trace of recursive HRS addition -/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit GateSpec

/-- Every bridge and child retains its original chronological position through width transport. -/
lemma hrsOneDirtyGates_trace (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyGates width constant).map (event .empty) =
      (oneDirtyProgram width constant).eventTrace := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
      by_cases base : width ≤ 1
      · rw [oneDirtyGates, dif_pos base, oneDirtyProgram, dif_pos base,
          oneDirtyBaseProgram, programList_eventTrace]
      · rw [oneDirtyGates, dif_neg base, hrsRecursiveStepGates_events]
        have decrease := hrsSplit_decreases width (by omega)
        rw [ih (lowWidth width) decrease.1, ih (highWidth width) decrease.2]
        conv_rhs => rw [oneDirtyProgram, dif_neg base]
        rw [recursiveStepProgram, joinProgram,
          UnitaryCircuit.castCanonicalQubitWidth_eventTrace]
        change _ =
          ((recursiveBridgeProgram width ((splitWord width) constant).1).eventTrace ++
            (placeLowChild (lowWidth width) (highWidth width)
              (oneDirtyProgram (lowWidth width) ((splitWord width) constant).1)).eventTrace) ++
            (placeHighChild (lowWidth width) (highWidth width)
              (oneDirtyProgram (highWidth width) ((splitWord width) constant).2)).eventTrace
        erw [placeLowChild, UnitaryCircuit.castCanonicalQubitWidth_eventTrace,
          UnitaryCircuit.onCanonicalBinarySuffix,
          UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventTrace,
          placeHighChild, UnitaryCircuit.unitaryCircuit_onBinaryMiddle_eventTrace]
        rfl


end

end QuantumAlg.MAU.Addition.HRS
