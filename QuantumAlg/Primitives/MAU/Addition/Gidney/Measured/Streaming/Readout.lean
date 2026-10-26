/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Step
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Composition

/-!
# Actual streaming-row projections and the retained vent character

The native compute row writes the outgoing carry before the incoming helper
is extracted and physically reset. The exact branch factor therefore reads
the original incoming helper of this row. These equations retain arbitrary
dirty and untouched encoded values [G25, main.tex:199-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete compute row preserves every projection insensitive to its outgoing flip. -/
lemma computeCarryGates_preserves (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) {Value : Type}
    (project : Data → Value)
    (untouched : ∀ state, project ((layout.nextCarry wide index).flip state) = project state)
    (state : Data) :
    project (stepList (layout.computeCarryGates wide constant index) state) = project state := by
  rw [computeCarryGates_step]
  split_ifs <;> first | exact untouched state | rfl

/-- Both extraction targets retain every projection insensitive to their two flips. -/
lemma extractCarryGates_preserves (layout : Layout encoding width)
    (index : Fin (width - 1)) {Value : Type} (project : Data → Value)
    (targetUntouched : ∀ state,
      project ((layout.target ⟨index.val, by omega⟩).flip state) = project state)
    (dirtyUntouched : ∀ (positive : 0 < index.val) state,
      project ((layout.dirty ⟨index.val - 1, by omega⟩).flip state) = project state)
    (state : Data) :
    project (stepList (layout.extractCarryGates index) state) = project state := by
  by_cases positive : 0 < index.val
  · rw [extractCarryGates_step layout index positive]
    split_ifs
    · rw [dirtyUntouched positive, targetUntouched]
    · rfl
  · rw [extractCarryGates_step_zero layout index (by omega)]

/-- The carry-compute row leaves the incoming helper available for extraction and venting. -/
lemma computeCarryGates_incoming (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    (layout.carryHelper index.val).get
        (stepList (layout.computeCarryGates wide constant index) state) =
      (layout.carryHelper index.val).get state :=
  computeCarryGates_preserves layout wide constant index (layout.carryHelper index.val).get
    (get_flip_of_wire_ne (layout.nextCarry wide index) (layout.carryHelper index.val)
      (layout.carryHelper_nextCarry_ne wide index).symm) state

/-- Both extraction CNOTs retain their original incoming-carry control. -/
lemma extractCarryGates_incoming (layout : Layout encoding width)
    (index : Fin (width - 1)) (state : Data) :
    (layout.carryHelper index.val).get (stepList (layout.extractCarryGates index) state) =
      (layout.carryHelper index.val).get state :=
  extractCarryGates_preserves layout index (layout.carryHelper index.val).get
    (get_flip_of_wire_ne (layout.target _) (layout.carryHelper index.val)
      (layout.target_clean_ne _ _))
    (fun _ => get_flip_of_wire_ne (layout.dirty _) (layout.carryHelper index.val)
      (layout.dirty_clean_ne _ _)) state

/-- Every positive row pays one actual vent with the exact original incoming-helper character. -/
lemma streamingStep_weight (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1))
    (outcome : Fin (width - 2) → Fin 2) (state : Data) :
    wordWeight outcome (layout.streamingStep wide constant index) state =
      if positive : 0 < index.val then
        NormalizedVector.invSqrt2 * MeasuredUncompute.character
          (outcome ⟨index.val - 1, by omega⟩) ((layout.carryHelper index.val).get state)
      else 1 := by
  by_cases positive : 0 < index.val
  · rw [streamingStep, dif_pos positive, dif_pos positive]
    simp only [List.cons_append, List.nil_append, wordWeight, branchWeight,
      labelStep, one_mul, mul_one]
    rw [extractCarryGates_incoming, computeCarryGates_incoming]
  · rw [streamingStep, dif_neg positive, dif_neg positive]
    simp only [List.cons_append, List.nil_append, wordWeight, branchWeight, one_mul]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
