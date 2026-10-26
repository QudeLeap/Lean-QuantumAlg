/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates.Support

/-!
# Literal placed TTK gate words with exact full-frame semantics

The source low-word generator is placed on the same actual two words.
This native word supports additional coherent controls without treating
a mathematical arithmetic update or a physical wire permutation as a
free operation. Its existing complete complement remains present.
-/

namespace QuantumAlg.MAU.Addition.TTK.WordPlacement

noncomputable section

open EncodedBit

variable {Data : Type} {frame : BinaryLabelEncoding Data} {width : Nat}
  (placement : WordPlacement frame width)

/-- Every literal source primitive is emitted on the two declared original operand words. -/
def nativeGates : List (GateSpec frame) :=
  (lowRippleGates width).map (placement.subsystem.placeGate source_onto placement.onto)

/-- The complete actual native word performs the same two-word arithmetic and complement action. -/
lemma nativeGates_step (state : Data) :
    GateSpec.stepList placement.nativeGates state = placement.step state := by
  rw [nativeGates, WireSubsystem.placeGates_step]
  simp only [ttkLowRipple_step]
  rfl

/-- An actual excluded position is outside every emitted native operand, including controls. -/
lemma nativeGates_bitDisjoint (observed : EncodedBit frame)
    (firstOutside : ∀ index, (placement.addend.bit index).wire ≠ observed.wire)
    (secondOutside : ∀ index, (placement.target.bit index).wire ≠ observed.wire)
    (gate : GateSpec frame) (present : gate ∈ placement.nativeGates) :
    GateSpec.bitDisjoint observed gate := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp present
  apply WireSubsystem.placeGate_bitDisjoint
  change ∀ index : Fin (width + width), placement.subsystem.wires index ≠ observed.wire
  apply Fin.addCases
  · intro index
    change (wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd width index) ≠ observed.wire
    rw [wordPairSubsystem_left]
    exact firstOutside index
  · intro index
    change (wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd width index) ≠ observed.wire
    rw [wordPairSubsystem_right]
    exact secondOutside index

/-- Literal native placement retains every original event coordinate without allocation. -/
lemma nativeGates_eventTrace :
    (placement.nativeGates.map (GateSpec.event .empty)) =
      ((lowRippleGates width).map (GateSpec.event .empty)) := by
  simp only [nativeGates, List.map_map, Function.comp_def, WireSubsystem.placeGate_event]

end

end QuantumAlg.MAU.Addition.TTK.WordPlacement
