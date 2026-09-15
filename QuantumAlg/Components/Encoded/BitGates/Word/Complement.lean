/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Complement every bit of an actual encoded word

One literal X gate acts at each supplied word position. Distinct physical
positions ensure each word bit is toggled exactly once. The reversed actual
list restores the entire encoded state, not merely the word's readout.
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- One actual X at each original word position, in the given word order. -/
def complementGates (word : Word encoding width) : List (GateSpec encoding) :=
  (List.ofFn fun index : Fin width => index).map fun index => .x (word.bit index)

/-- The actual gate list has one occurrence for every word bit. -/
theorem complementGates_length (word : Word encoding width) :
    word.complementGates.length = width := by
  simp [complementGates]

private theorem complementGates_step (word : Word encoding width) (state : Data) :
    GateSpec.stepList word.complementGates state =
      word.xorConstantIndicesStep (List.ofFn fun index : Fin width => index) state := by
  rw [GateSpec.stepList_eq_foldl, complementGates, List.foldl_map]
  rfl

/-- Every distinct physical word position is complemented exactly once. -/
theorem complementGates_get (word : Word encoding width)
    (distinct : Function.Injective (fun index => (word.bit index).wire))
    (state : Data) (index : Fin width) :
    (word.bit index).get (GateSpec.stepList word.complementGates state) =
      !(word.bit index).get state := by
  rw [complementGates_step]
  rw [xorConstantIndicesStep_get_target word _
    (List.nodup_ofFn_ofInjective (fun _ _ same => same)) index
    (fun other different same => different (distinct same))]
  have present : index ∈ (List.ofFn fun index : Fin width => index) :=
    List.mem_ofFn.mpr ⟨index, rfl⟩
  simp only [decide_eq_true present, Bool.xor_true]

/-- Every other actual encoded bit keeps its original value. -/
theorem complementGates_get_other (word : Word encoding width)
    (observed : EncodedBit encoding)
    (different : ∀ index, (word.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (GateSpec.stepList word.complementGates state) = observed.get state := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate present
  obtain ⟨index, _present, rfl⟩ := List.mem_map.mp present
  exact get_flip_of_wire_ne (word.bit index) observed (different index)

/-- Reversing the same complement list restores every original encoded coordinate. -/
theorem complementGates_reverse_restore (word : Word encoding width) (state : Data) :
    GateSpec.stepList word.complementGates.reverse
        (GateSpec.stepList word.complementGates state) = state :=
  GateSpec.stepList_reverse_stepList word.complementGates state

end

end QuantumAlg.EncodedBit.Word
