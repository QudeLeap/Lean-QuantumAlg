/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Transition

/-!
# Exact outgoing-carry readout through the actual physical reset row

The original outgoing system survives both extraction CNOTs and the reset of
the other helper. Only the paid final affine CNOT completes its value. The
statement applies to an arbitrary original outgoing and dirty value, including
the final original target high bit [G25, main.tex:209-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every original dirty output is physically distinct from the row's outgoing carry system. -/
lemma dirty_nextCarry_ne (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 1)) (dirtyIndex : Fin (width - 2)) :
    (layout.dirty dirtyIndex).wire ≠ (layout.nextCarry wide index).wire := by
  unfold nextCarry
  split_ifs
  · exact layout.dirty_clean_ne _ _
  · exact (layout.target_dirty_ne _ _).symm

/-- The final native CNOT xors the same selected static bit into the outgoing carry. -/
lemma finishCarryGates_outgoing (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    (layout.nextCarry wide index).get
        (stepList (layout.finishCarryGates wide constant index) state) =
      ((layout.nextCarry wide index).get state ^^
        (constant.getLsbD index.val && layout.control.get state)) := by
  rw [finishCarryGates_step]
  generalize product : (constant.getLsbD index.val && layout.control.get state) = fired
  cases fired <;> simp [get_flip_self]

private lemma reset_other (target observed : EncodedBit encoding)
    (different : target.wire ≠ observed.wire) (state : Data) :
    observed.get (MeasuredUncompute.resetLabel target state) = observed.get state := by
  unfold MeasuredUncompute.resetLabel
  split_ifs
  · exact get_flip_of_wire_ne target observed different state
  · rfl

/-- Every chronological row has the exact affine outgoing action before its carry invariant. -/
lemma streamingStep_outgoing (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    (layout.nextCarry wide index).get
        (wordLabel (layout.streamingStep wide constant index) state) =
      (((layout.nextCarry wide index).get state ^^
        ((layout.target ⟨index.val, by omega⟩).get state &&
          (if index.val = 0 then constant.getLsbD index.val && layout.control.get state
           else (layout.carryHelper index.val).get state ^^
             (constant.getLsbD index.val && layout.control.get state)))) ^^
        (constant.getLsbD index.val && layout.control.get state)) := by
  let before := stepList (layout.extractCarryGates index)
    (stepList (layout.computeCarryGates wide constant index) state)
  let cleared := if 0 < index.val then
    MeasuredUncompute.resetLabel (layout.carryHelper index.val) before else before
  have control : layout.control.get cleared = layout.control.get state := by
    have actual := streamingStep_control_get layout wide constant index state
    rw [streamingStep_label,
      finishCarryGates_preserves layout wide constant index layout.control.get
        (get_flip_of_wire_ne (layout.nextCarry wide index) layout.control
          (layout.control_nextCarry_ne wide index).symm)] at actual
    exact actual
  have extraction : (layout.nextCarry wide index).get before =
      (layout.nextCarry wide index).get
        (stepList (layout.computeCarryGates wide constant index) state) :=
    extractCarryGates_preserves layout index (layout.nextCarry wide index).get
      (get_flip_of_wire_ne (layout.target _) (layout.nextCarry wide index)
        (layout.target_nextCarry_ne wide index))
      (fun _ => get_flip_of_wire_ne (layout.dirty _) (layout.nextCarry wide index)
        (layout.dirty_nextCarry_ne wide index _)) _
  have clearing : (layout.nextCarry wide index).get cleared =
      (layout.nextCarry wide index).get before := by
    dsimp only [cleared]
    split_ifs
    · exact reset_other (layout.carryHelper index.val) (layout.nextCarry wide index)
        (layout.carryHelper_nextCarry_ne wide index) before
    · rfl
  rw [streamingStep_label, finishCarryGates_outgoing]
  change ((layout.nextCarry wide index).get cleared ^^
    (constant.getLsbD index.val && layout.control.get cleared)) = _
  rw [control, clearing, extraction, computeCarryGates_outgoing]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
