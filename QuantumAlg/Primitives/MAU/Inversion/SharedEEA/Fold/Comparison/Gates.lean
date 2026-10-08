/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Placement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Literal comparison and reflection instructions on the complete shared frame

The actual focus permutation, middle insertion, Work1 prefix and equal-width
regrouping transport each primitive to its original physical wire. Every
complementary field is retained, with no input-value or cleanliness premise.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonPlacement

noncomputable section

open EncodedBit GateSpec

/-- The packed tensor frame and original source frame have identical labels at identical wires. -/
def packedPlacement (width : Nat) : FullPlacement (packedEncoding width) (encoding width) :=
  FullPlacement.ofEqualWidth _ _ (packedEquiv width) (packed_width width)
    (packedIndex_encode width)

private theorem inserted_event {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    (middle : BinaryLabelEncoding Middle) (gate : GateSpec (BinaryLabelEncoding.prod left right)) :
    (GateSpec.insertMiddle middle gate).event .empty = gate.event .empty := by
  cases gate <;> rfl

/-- Relocate every original Gidney instruction across all retained shared-register spectators. -/
def placeGates (width : Nat)
    (instructions : List (GateSpec (Addition.Gidney.encoding (width + 3)))) :
    List (GateSpec (encoding width)) :=
  (((instructions.map (FoldComparisonFocus.placement (width + 3)).placeGate).map
    (GateSpec.insertMiddle (middleEncoding width))).map
      (GateSpec.prodRight (wordEncoding (width + 3)))).map
        (packedPlacement width).placeGate

/-- The complete emitted word acts through the same original full semantic grouping. -/
theorem foldComparison_placeGates_step (width : Nat)
    (instructions : List (GateSpec (Addition.Gidney.encoding (width + 3))))
    (state : Registers width) :
    stepList (placeGates width instructions) state =
      (FoldRegisters.grouping width).symm
        (stepList instructions (FoldRegisters.grouping width state).1,
          (FoldRegisters.grouping width state).2) := by
  erw [placeGates, FullPlacement.placeGates_step]
  have grouping : (packedPlacement width).grouping = packedEquiv width :=
    FullPlacement.ofEqualWidth_grouping _ _ _ _ _
  simp only [FullPlacement.step, grouping]
  erw [stepList_prodRight, stepList_insertMiddle, FullPlacement.placeGates_step]
  unfold FullPlacement.step
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  rfl

/-- The literal placement preserves the chronological native event word without added swaps. -/
theorem foldComparison_placeGates_trace (width : Nat)
    (instructions : List (GateSpec (Addition.Gidney.encoding (width + 3)))) :
    (placeGates width instructions).map (event .empty) = instructions.map (event .empty) := by
  unfold placeGates
  erw [List.map_map, List.map_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro gate _
  exact ((packedPlacement width).placeGate_event .empty _).trans
    ((event_prodRight _ _).trans
      ((inserted_event _ _).trans
        ((FoldComparisonFocus.placement (width + 3)).placeGate_event .empty gate)))

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonPlacement
