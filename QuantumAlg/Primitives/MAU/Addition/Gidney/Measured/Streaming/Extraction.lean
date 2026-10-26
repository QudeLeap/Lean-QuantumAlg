/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Ports

/-!
# Actual carry extraction and incoming-helper physical reset

Each positive row xors the same incoming carry into its original target and
dirty bit. Its later physical reset leaves that helper at zero. The outgoing
carry uses a different system [G25, main.tex:239-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma reset_get (target : EncodedBit encoding) (state : Data) :
    target.get (MeasuredUncompute.resetLabel target state) = false := by
  unfold MeasuredUncompute.resetLabel
  cases value : target.get state <;> simp [value, get_flip_self]

private lemma reset_get_other (target observed : EncodedBit encoding)
    (different : target.wire ≠ observed.wire) (state : Data) :
    observed.get (MeasuredUncompute.resetLabel target state) = observed.get state := by
  unfold MeasuredUncompute.resetLabel
  split_ifs
  · exact get_flip_of_wire_ne target observed different state
  · rfl

/-- The original target receives exactly the retained incoming carry through the first CNOT. -/
lemma extractCarryGates_target (layout : Layout encoding width) (index : Fin (width - 1))
    (positive : 0 < index.val) (state : Data) :
    (layout.target ⟨index.val, by omega⟩).get (stepList (layout.extractCarryGates index) state) =
      ((layout.target ⟨index.val, by omega⟩).get state ^^
        (layout.carryHelper index.val).get state) := by
  rw [extractCarryGates, dif_pos positive]
  change (layout.target ⟨index.val, by omega⟩).get
    (cnotStep (layout.carryHelper index.val) (layout.dirty ⟨index.val - 1, by omega⟩)
      (cnotStep (layout.carryHelper index.val) (layout.target ⟨index.val, by omega⟩) state)) = _
  rw [cnotStep_get_of_target_ne _ _ _ (layout.target_dirty_ne _ _).symm,
    cnotStep_get_target]

/-- The original arbitrary dirty bit receives exactly the same incoming carry through the second. -/
lemma extractCarryGates_dirty (layout : Layout encoding width) (index : Fin (width - 1))
    (positive : 0 < index.val) (state : Data) :
    (layout.dirty ⟨index.val - 1, by omega⟩).get
        (stepList (layout.extractCarryGates index) state) =
      ((layout.dirty ⟨index.val - 1, by omega⟩).get state ^^
        (layout.carryHelper index.val).get state) := by
  rw [extractCarryGates, dif_pos positive]
  change (layout.dirty ⟨index.val - 1, by omega⟩).get
    (cnotStep (layout.carryHelper index.val) (layout.dirty ⟨index.val - 1, by omega⟩)
      (cnotStep (layout.carryHelper index.val) (layout.target ⟨index.val, by omega⟩) state)) = _
  rw [cnotStep_get_target,
    cnotStep_get_of_target_ne _ _ _ (layout.target_dirty_ne _ _),
    cnotStep_get_of_target_ne (layout.carryHelper index.val) (layout.target _)
      (layout.carryHelper index.val) (layout.target_clean_ne _ _)]

/-- The complete positive row physically resets its incoming helper after extraction. -/
lemma streamingStep_incoming_zero (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (positive : 0 < index.val)
    (state : Data) :
    (layout.carryHelper index.val).get
      (wordLabel (layout.streamingStep wide constant index) state) = false := by
  rw [streamingStep_label, if_pos positive,
    finishCarryGates_preserves layout wide constant index (layout.carryHelper index.val).get
      (get_flip_of_wire_ne (layout.nextCarry wide index) (layout.carryHelper index.val)
        (layout.carryHelper_nextCarry_ne wide index).symm), reset_get]

/-- The complete row xors the original incoming carry into its addressed target bit. -/
lemma streamingStep_target (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    (layout.target ⟨index.val, by omega⟩).get
        (wordLabel (layout.streamingStep wide constant index) state) =
      ((layout.target ⟨index.val, by omega⟩).get state ^^
        (if 0 < index.val then (layout.carryHelper index.val).get state else false)) := by
  rw [streamingStep_label,
    finishCarryGates_preserves layout wide constant index
      (layout.target ⟨index.val, by omega⟩).get
      (get_flip_of_wire_ne (layout.nextCarry wide index) (layout.target _)
        (layout.target_nextCarry_ne wide index).symm)]
  by_cases positive : 0 < index.val
  · rw [if_pos positive, if_pos positive,
      reset_get_other (layout.carryHelper index.val) (layout.target _)
        (layout.target_clean_ne _ _).symm,
      extractCarryGates_target layout index positive,
      computeCarryGates_preserves layout wide constant index (layout.target _).get
        (get_flip_of_wire_ne (layout.nextCarry wide index) (layout.target _)
          (layout.target_nextCarry_ne wide index).symm),
      computeCarryGates_incoming]
  · rw [if_neg positive, if_neg positive, extractCarryGates_step_zero layout index (by omega),
      computeCarryGates_preserves layout wide constant index (layout.target _).get
        (get_flip_of_wire_ne (layout.nextCarry wide index) (layout.target _)
          (layout.target_nextCarry_ne wide index).symm), Bool.xor_false]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
