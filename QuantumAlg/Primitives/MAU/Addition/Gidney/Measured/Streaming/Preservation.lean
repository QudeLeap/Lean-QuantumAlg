/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Extraction

/-!
# Complete projection preservation through the actual measured row

Only its outgoing carry, source target, incoming helper and matching dirty bit
can change. Insensitive projections retain their exact arbitrary value through
the actual compute/extract/physical-reset/finish order
[G25, main.tex:209-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma reset_preserves (target : EncodedBit encoding) {Value : Type}
    (project : Data → Value)
    (untouched : ∀ state, project (target.flip state) = project state) (state : Data) :
    project (MeasuredUncompute.resetLabel target state) = project state := by
  unfold MeasuredUncompute.resetLabel
  split_ifs
  · exact untouched state
  · rfl

/-- Every projection insensitive to the row's actual writes is retained by the complete row. -/
lemma streamingStep_preserves (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) {Value : Type}
    (project : Data → Value)
    (nextUntouched : ∀ state,
      project ((layout.nextCarry wide index).flip state) = project state)
    (targetUntouched : ∀ state,
      project ((layout.target ⟨index.val, by omega⟩).flip state) = project state)
    (dirtyUntouched : ∀ (positive : 0 < index.val) state,
      project ((layout.dirty ⟨index.val - 1, by omega⟩).flip state) = project state)
    (helperUntouched : ∀ (_positive : 0 < index.val) state,
      project ((layout.carryHelper index.val).flip state) = project state)
    (state : Data) :
    project (wordLabel (layout.streamingStep wide constant index) state) = project state := by
  rw [streamingStep_label,
    finishCarryGates_preserves layout wide constant index project nextUntouched]
  by_cases positive : 0 < index.val
  · rw [if_pos positive, reset_preserves (layout.carryHelper index.val) project
      (helperUntouched positive),
      extractCarryGates_preserves layout index project targetUntouched dirtyUntouched,
      computeCarryGates_preserves layout wide constant index project nextUntouched]
  · rw [if_neg positive,
      extractCarryGates_preserves layout index project targetUntouched dirtyUntouched,
      computeCarryGates_preserves layout wide constant index project nextUntouched]

/-- The incoming helper is zeroed in every positive row and retained in the first row. -/
lemma streamingStep_incoming (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    (layout.carryHelper index.val).get
        (wordLabel (layout.streamingStep wide constant index) state) =
      if 0 < index.val then false else (layout.carryHelper index.val).get state := by
  by_cases positive : 0 < index.val
  · rw [if_pos positive, streamingStep_incoming_zero layout wide constant index positive]
  · rw [if_neg positive, streamingStep_label, if_neg positive,
      finishCarryGates_preserves layout wide constant index (layout.carryHelper index.val).get
        (get_flip_of_wire_ne (layout.nextCarry wide index) (layout.carryHelper index.val)
          (layout.carryHelper_nextCarry_ne wide index).symm),
      extractCarryGates_incoming, computeCarryGates_incoming]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
