/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Readout

/-!
# Chronological label transition of one actual vented carry row

The outgoing carry is computed before the incoming helper is extracted and
physically reset. The final affine CNOT uses the retained original quantum
control [G25, main.tex:209-251,354-360].
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

/-- The actual row retains its literal compute/extract/reset/finish label order. -/
lemma streamingStep_label (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    wordLabel (layout.streamingStep wide constant index) state =
      stepList (layout.finishCarryGates wide constant index)
        (if 0 < index.val then
          MeasuredUncompute.resetLabel (layout.carryHelper index.val)
            (stepList (layout.extractCarryGates index)
              (stepList (layout.computeCarryGates wide constant index) state))
        else stepList (layout.extractCarryGates index)
          (stepList (layout.computeCarryGates wide constant index) state)) := by
  by_cases positive : 0 < index.val <;>
    simp only [streamingStep, positive, dite_true, dite_false, ite_true, ite_false,
      List.cons_append, List.nil_append, wordLabel, labelStep]

/-- The actual finish row preserves every projection insensitive to its outgoing flip. -/
lemma finishCarryGates_preserves (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) {Value : Type}
    (project : Data → Value)
    (untouched : ∀ state, project ((layout.nextCarry wide index).flip state) = project state)
    (state : Data) :
    project (stepList (layout.finishCarryGates wide constant index) state) = project state := by
  rw [finishCarryGates_step]
  split_ifs
  · exact untouched state
  · rfl

/-- The same original coherent quantum control is retained by the complete measured row. -/
lemma streamingStep_control_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    layout.control.get (wordLabel (layout.streamingStep wide constant index) state) =
      layout.control.get state := by
  rw [streamingStep_label,
    finishCarryGates_preserves layout wide constant index layout.control.get
      (get_flip_of_wire_ne (layout.nextCarry wide index) layout.control
        (layout.control_nextCarry_ne wide index).symm)]
  split_ifs
  · rw [reset_preserves (layout.carryHelper index.val) layout.control.get
      (get_flip_of_wire_ne (layout.carryHelper index.val) layout.control
        (layout.control_clean_ne _).symm)]
    rw [extractCarryGates_preserves layout index layout.control.get
      (get_flip_of_wire_ne (layout.target _) layout.control
        (layout.control_target_ne _).symm)
      (fun _ => get_flip_of_wire_ne (layout.dirty _) layout.control
        (layout.control_dirty_ne _).symm)]
    exact computeCarryGates_preserves layout wide constant index layout.control.get
      (get_flip_of_wire_ne (layout.nextCarry wide index) layout.control
        (layout.control_nextCarry_ne wide index).symm) state
  · rw [extractCarryGates_preserves layout index layout.control.get
      (get_flip_of_wire_ne (layout.target _) layout.control
        (layout.control_target_ne _).symm)
      (fun _ => get_flip_of_wire_ne (layout.dirty _) layout.control
        (layout.control_dirty_ne _).symm)]
    exact computeCarryGates_preserves layout wide constant index layout.control.get
      (get_flip_of_wire_ne (layout.nextCarry wide index) layout.control
        (layout.control_nextCarry_ne wide index).symm) state

/-- The actual compute row xors its original affine Boolean product into the outgoing system. -/
lemma computeCarryGates_outgoing (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    (layout.nextCarry wide index).get
        (stepList (layout.computeCarryGates wide constant index) state) =
      ((layout.nextCarry wide index).get state ^^
        ((layout.target ⟨index.val, by omega⟩).get state &&
          (if index.val = 0 then constant.getLsbD index.val && layout.control.get state
           else (layout.carryHelper index.val).get state ^^
             (constant.getLsbD index.val && layout.control.get state)))) := by
  rw [computeCarryGates_step]
  generalize product :
    ((layout.target ⟨index.val, by omega⟩).get state &&
      (if index.val = 0 then constant.getLsbD index.val && layout.control.get state
       else (layout.carryHelper index.val).get state ^^
         (constant.getLsbD index.val && layout.control.get state))) = fired
  cases fired <;> simp [get_flip_self]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
