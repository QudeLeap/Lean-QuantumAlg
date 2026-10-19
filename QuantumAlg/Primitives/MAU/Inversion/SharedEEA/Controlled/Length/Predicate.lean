/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Pattern
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Predicate

/-!
# Actual retained-Ctrl length predicates with the original dirty Iter

Each boundary and leading-one candidate reads original Ctrl as one extra
positive source control of the existing actual one-dirty pattern. Its
target remains an actual length-field bit, and arbitrary original Iter
remains the sole restored work bit. No second dirty bit is needed.

The current divisor length can therefore change during its real refresh
without changing the selecting Ctrl. The higher-level boundary program
computes that Ctrl before exchanging the work words and updating the
lengths in source order [LYL+26, sec_EEA/sub_regshare.tex:310-314;
LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341]. This owner supplies
the exact physical candidate; it does not assume a boundary predicate or
claim that an arbitrary boundary frame cleans its selecting Ctrl.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthPredicate

noncomputable section

open EncodedBit LengthCoordinates

private lemma control_source_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (index : Fin (width.size + region width field key)) :
    (controlBit width).wire ≠ (sourceBit width field key firstWord index).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [controlBit_wire] at values
  unfold sourceBit at values
  split at values
  · rw [boundaryBit_wire] at values
    split_ifs at values <;> omega
  · have before := payloadBit_before_lengths width field key firstWord
      ⟨index.val - width.size, by have within := index.isLt; omega⟩
    omega

private lemma control_output_ne (width : Nat) (field : Field) (output : Fin width.size) :
    (controlBit width).wire ≠ (outputBit width field output).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  have within := output.rev.isLt
  cases field <;> simp only [outputBit, coefficientLengthBit_wire,
    divisorLengthBit_wire, controlBit_wire] at values <;> omega

private lemma control_work_ne (width : Nat) :
    (controlBit width).wire ≠ (iterationBit width).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [controlBit_wire, iterationBit_wire] at values
  omega

/-- The candidate's real existing prefix sources are physically separate from original Ctrl. -/
lemma leading_source_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (output : Fin width.size)
    (index : Fin (width.size + (position.val + 1))) :
    (controlBit width).wire ≠
      (((layout width field key firstWord output).leadingLayout position).source.bit index).wire :=
  control_source_ne width field key firstWord (Word.OneDirtyLayout.sourceIndex position index)

/-- One actual enlarged pattern, with original Ctrl positive and all original candidate bits. -/
def gates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    List (GateSpec (encoding width)) :=
  ((layout width field key firstWord output).leadingLayout position).controlledPatternGates
    (controlBit width) (leading_source_ne width field key firstWord position output)
    (control_output_ne width field output) (control_work_ne width)
    (Word.OneDirtyLayout.leadingPattern position (fun index => key.getMsbD index.val))

/-- Actual complete-frame execution tests retained Ctrl and the true current leading-one value. -/
lemma gates_step (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width field key firstWord position output) state =
      if state.control then
        (if LengthPredicate.Selected field key firstWord position state
          then (outputBit width field output).flip state else state)
      else state := by
  have actual :=
    ((layout width field key firstWord output).leadingLayout position).controlledPatternGates_step
      (controlBit width) (leading_source_ne width field key firstWord position output)
      (control_output_ne width field output) (control_work_ne width)
      (Word.OneDirtyLayout.leadingPattern position (fun index => key.getMsbD index.val)) state
  have selectedOutput :
      ((layout width field key firstWord output).leadingLayout position).output =
        outputBit width field output := rfl
  simpa only [gates, controlBit_get, Word.OneDirtyLayout.leadingPattern_iff,
    LengthPredicate.leading_iff, selectedOutput] using actual

/-- The same actual candidate is the retained-control refinement of the existing length writer. -/
lemma gates_step_if (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width field key firstWord position output) state =
      if state.control then
        GateSpec.stepList (LengthPredicate.gates width field key firstWord position output) state
      else state := by
  rw [gates_step, LengthPredicate.gates_step]

/-- Each original candidate preserves the selecting Ctrl, even when its length target changes. -/
lemma original_control (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    (GateSpec.stepList (LengthPredicate.gates width field key firstWord position output)
      state).control = state.control := by
  rw [LengthPredicate.gates_step]
  split
  · exact get_flip_of_wire_ne (outputBit width field output) (controlBit width)
      (control_output_ne width field output).symm state
  · rfl

/-- Original arbitrary Iter is restored by every emitted controlled candidate. -/
lemma gates_iteration (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    (GateSpec.stepList (gates width field key firstWord position output) state).flags.iteration =
      state.flags.iteration :=
  ((layout width field key firstWord output).leadingLayout position).controlledPatternGates_work
    (controlBit width) (leading_source_ne width field key firstWord position output)
    (control_output_ne width field output) (control_work_ne width)
    (Word.OneDirtyLayout.leadingPattern position (fun index => key.getMsbD index.val)) state

/-- Count every actual source bit, including Ctrl, both masks, and dirty Iter cleanup. -/
lemma gates_length_le (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    (gates width field key firstWord position output).length ≤
      10 * (width.size + (position.val + 1) + 1) + 1 :=
  Word.OneDirtyLayout.controlledPatternGates_length_le
    ((layout width field key firstWord output).leadingLayout position)
    (controlBit width) (leading_source_ne width field key firstWord position output)
    (control_output_ne width field output) (control_work_ne width)
    (Word.OneDirtyLayout.leadingPattern position (fun index => key.getMsbD index.val))

/-- Actual unit depth is the emitted candidate's elementary length. -/
lemma gates_unitDepth (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    (GateSpec.programList (QubitLayout.canonical _) .empty
      (gates width field key firstWord position output)).evaluatedEventDepth
        (fun _ => 1) = (gates width field key firstWord position output).length :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthPredicate
