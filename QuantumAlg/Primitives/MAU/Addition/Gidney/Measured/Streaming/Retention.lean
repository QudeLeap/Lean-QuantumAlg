/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Preservation

/-!
# Original target, dirty and outside-wire retention by each actual row

Readouts outside the row's physical writes retain their complete arbitrary
original values. The laws use addressed physical-wire separation, including
the final outgoing carry in the original target high bit
[G25, main.tex:239-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every target outside the extraction source and outgoing carry is retained by the actual row. -/
lemma streamingStep_target_other (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (observed : Fin width)
    (sourceDifferent : index.val ≠ observed.val)
    (nextDifferent : (layout.nextCarry wide index).wire ≠ (layout.target observed).wire)
    (state : Data) :
    (layout.target observed).get (wordLabel (layout.streamingStep wide constant index) state) =
      (layout.target observed).get state :=
  streamingStep_preserves layout wide constant index (layout.target observed).get
    (get_flip_of_wire_ne _ _ nextDifferent)
    (get_flip_of_wire_ne _ _ (layout.target_target_ne (fun same =>
      sourceDifferent (congrArg Fin.val same))))
    (fun _ => get_flip_of_wire_ne _ _ (layout.target_dirty_ne _ _).symm)
    (fun _ => get_flip_of_wire_ne _ _ (layout.target_clean_ne _ _).symm) state

/-- Every original dirty output except the positive row's extraction output is retained. -/
lemma streamingStep_dirty_other (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (observed : Fin (width - 2))
    (different : 0 < index.val → index.val - 1 ≠ observed.val) (state : Data) :
    (layout.dirty observed).get (wordLabel (layout.streamingStep wide constant index) state) =
      (layout.dirty observed).get state :=
  streamingStep_preserves layout wide constant index (layout.dirty observed).get
    (get_flip_of_wire_ne _ _ (layout.dirty_nextCarry_ne wide index observed).symm)
    (get_flip_of_wire_ne _ _ (layout.target_dirty_ne _ _))
    (fun positive => get_flip_of_wire_ne _ _ (layout.dirty_dirty_ne (fun same =>
      different positive (congrArg Fin.val same))))
    (fun _ => get_flip_of_wire_ne _ _ (layout.dirty_clean_ne _ _).symm) state

/-- The complete positive row xors its original incoming carry into the original dirty output. -/
lemma streamingStep_dirty (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (positive : 0 < index.val)
    (state : Data) :
    (layout.dirty ⟨index.val - 1, by omega⟩).get
        (wordLabel (layout.streamingStep wide constant index) state) =
      ((layout.dirty ⟨index.val - 1, by omega⟩).get state ^^
        (layout.carryHelper index.val).get state) := by
  rw [streamingStep_label, if_pos positive,
    finishCarryGates_preserves layout wide constant index (layout.dirty _).get
      (get_flip_of_wire_ne _ _ (layout.dirty_nextCarry_ne wide index _).symm)]
  have resetRead (current : Data) :
      (layout.dirty ⟨index.val - 1, by omega⟩).get
          (MeasuredUncompute.resetLabel (layout.carryHelper index.val) current) =
        (layout.dirty ⟨index.val - 1, by omega⟩).get current := by
    unfold MeasuredUncompute.resetLabel
    split_ifs
    · exact get_flip_of_wire_ne _ _ (layout.dirty_clean_ne _ _).symm current
    · rfl
  rw [resetRead, extractCarryGates_dirty layout index positive,
    computeCarryGates_preserves layout wide constant index (layout.dirty _).get
      (get_flip_of_wire_ne _ _ (layout.dirty_nextCarry_ne wide index _).symm),
    computeCarryGates_incoming]

/-- Every original encoded wire outside all supplied ports is retained by the actual row. -/
lemma streamingStep_wire_read (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (observed : Fin encoding.width)
    (outside : ∀ port, (layout.bit port).wire ≠ observed) (state : Data) :
    (encoding.encode (wordLabel (layout.streamingStep wide constant index) state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  let project := fun current : Data =>
    (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val
  have untouched (port : Port width) (current : Data) :
      project ((layout.bit port).flip current) = project current := by
    dsimp only [project]
    rw [(layout.bit port).encode_flip, WireAddress.bit_flipBit_of_ne (outside port)]
  apply streamingStep_preserves layout wide constant index project
  · unfold nextCarry
    split_ifs
    · exact untouched (.inr (.inr (.inr _)))
    · exact untouched (.inr (.inl _))
  · exact untouched (.inr (.inl _))
  · intro _
    exact untouched (.inr (.inr (.inl _)))
  · intro _
    exact untouched (.inr (.inr (.inr _)))

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
