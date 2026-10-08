/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Recursive.Placement
import all QuantumAlg.Primitives.MAU.Addition.HRS.JoinPlacement
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Literal gate placement for the recursive HRS children

The two children reuse the same dirty bit. Their gate lists retain physical
high/low bit order through the split and join, so later controlled constructions
can expand the actual source gates [HRS16, paper.tex:232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit GateSpec BinaryLabelEncoding

private def lowChildGrouping (low high : Nat) :
    BridgeRegisters (Fin (2 ^ low)) high ≃ Fin (2 ^ high) × OneDirtyRegisters low :=
  (bridgeGrouping low high).trans (Equiv.prodAssoc _ _ _)

private def lowChildPlacement (low high : Nat) :
    FullPlacement (prod (finIdentity high) (oneDirtyEncoding low))
      (bridgeEncoding low high) :=
  FullPlacement.ofEqualWidth _ _ (lowChildGrouping low high) (lowChildWidth low high)
    (by rintro ⟨⟨lowWord, highWord⟩, dirty⟩
        exact lowChildCastIndex_encode low high lowWord highWord dirty)

/-- Place the low child's literal gates while retaining the high word. -/
def lowChildGates (low high : Nat) (gates : List (GateSpec (oneDirtyEncoding low))) :
    List (GateSpec (bridgeEncoding low high)) :=
  (gates.map (GateSpec.prodRight (finIdentity high))).map
    (lowChildPlacement low high).placeGate

/-- The low child acts only on its own word and the shared dirty bit. -/
theorem hrsLowChildGates_step (low high : Nat)
    (gates : List (GateSpec (oneDirtyEncoding low)))
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    stepList (lowChildGates low high gates) state =
      let output := stepList gates (state.1.1, state.2)
      ((output.1, state.1.2), output.2) := by
  rw [lowChildGates, FullPlacement.placeGates_step]
  change (lowChildGrouping low high).symm
    (stepList (gates.map (GateSpec.prodRight (finIdentity high)))
      (lowChildGrouping low high state)) = _
  rw [stepList_prodRight]
  rfl

/-- The low child's complete event list is unchanged by placement. -/
theorem hrsLowChildGates_events (low high : Nat)
    (gates : List (GateSpec (oneDirtyEncoding low))) (oracles : OracleModel) :
    (lowChildGates low high gates).map (event oracles) = gates.map (event oracles) := by
  simp [lowChildGates, List.map_map, Function.comp_def]

/-- Place the high child's literal gates around the inactive low word. -/
def highChildGates (low high : Nat) (gates : List (GateSpec (oneDirtyEncoding high))) :
    List (GateSpec (bridgeEncoding low high)) :=
  (gates.map (GateSpec.insertMiddle (finIdentity low))).map
    (GateSpec.relabel (bridgeGrouping low high))

/-- The inserted low word is untouched by the high child's actual gates. -/
theorem hrsHighChildGates_step (low high : Nat)
    (gates : List (GateSpec (oneDirtyEncoding high)))
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    stepList (highChildGates low high gates) state =
      let output := stepList gates (state.1.2, state.2)
      ((state.1.1, output.1), output.2) := by
  exact (stepList_relabel (bridgeGrouping low high)
    (gates.map (GateSpec.insertMiddle (finIdentity low))) state).trans
      (congrArg (bridgeGrouping low high).symm
        (stepList_insertMiddle (finIdentity low) gates (bridgeGrouping low high state)))

private theorem insertMiddle_event {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    (middle : BinaryLabelEncoding Middle) (gate : GateSpec (prod left right))
    (oracles : OracleModel) :
    (GateSpec.insertMiddle middle gate).event oracles = gate.event oracles := by
  cases gate <;> rfl

/-- The high child's complete event list is unchanged by placement. -/
theorem hrsHighChildGates_events (low high : Nat)
    (gates : List (GateSpec (oneDirtyEncoding high))) (oracles : OracleModel) :
    (highChildGates low high gates).map (event oracles) = gates.map (event oracles) := by
  calc
    _ = (gates.map (GateSpec.insertMiddle (finIdentity low))).map (event oracles) :=
      map_event_relabel oracles (bridgeGrouping low high) _
    _ = gates.map (event oracles) := by
      induction gates with
      | nil => rfl
      | cons gate rest ih =>
          exact congrArg₂ List.cons (insertMiddle_event (finIdentity low) gate oracles) ih

private def joinGrouping (width : Nat) :
    OneDirtyRegisters width ≃ BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width) :=
  Equiv.prodCongr (splitWord width) (Equiv.refl Bool)

private def joinPlacement (width : Nat) :
    FullPlacement (bridgeEncoding (lowWidth width) (highWidth width))
      (oneDirtyEncoding width) :=
  FullPlacement.ofEqualWidth _ _ (joinGrouping width) (bridgeOneDirtyWidth width)
    (by rintro ⟨word, dirty⟩
        exact (joinCastIndex_encode width ((splitWord width) word) dirty).trans
          (congrArg (fun output => (oneDirtyEncoding width).encode (output, dirty))
            (hrsJoin_split width word)))

/-- Expose the unsplit word without changing any physical gate or adding storage. -/
def joinGates (width : Nat)
    (gates : List (GateSpec (bridgeEncoding (lowWidth width) (highWidth width)))) :
    List (GateSpec (oneDirtyEncoding width)) :=
  gates.map (joinPlacement width).placeGate

/-- The joined literal list implements the original split action on the original word. -/
theorem hrsJoinGates_step (width : Nat)
    (gates : List (GateSpec (bridgeEncoding (lowWidth width) (highWidth width))))
    (state : OneDirtyRegisters width) :
    stepList (joinGates width gates) state =
      let output := stepList gates ((splitWord width) state.1, state.2)
      (joinWord width output.1, output.2) := by
  rw [joinGates, FullPlacement.placeGates_step]
  simp only [FullPlacement.step, joinPlacement, FullPlacement.ofEqualWidth_grouping]
  rfl

/-- Joining retains the original ordered native events. -/
theorem hrsJoinGates_events (width : Nat)
    (gates : List (GateSpec (bridgeEncoding (lowWidth width) (highWidth width))))
    (oracles : OracleModel) :
    (joinGates width gates).map (event oracles) = gates.map (event oracles) := by
  simp [joinGates, List.map_map, Function.comp_def]

end

end QuantumAlg.MAU.Addition.HRS
