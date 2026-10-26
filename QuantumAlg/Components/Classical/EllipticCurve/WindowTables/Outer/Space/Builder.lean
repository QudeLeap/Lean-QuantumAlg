/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Arithmetic
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions

/-!
# Actual live capacity of the complete five-table builder

All original row slots, the forward/inverse/reverse batch and the final
identity writes reuse the same scalar scratch allowance. The five actual
arrays belong to the enclosing caller and remain fully live throughout.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

private lemma row_bound (instruction : RowInstruction ctx width length)
    (spec : ModulusSpec width) (modulus : CWriteRef ctx (.unsignedWord (width + 1))) :
    Bound (coefficientScratchSpace model.kind width)
      (instruction.circuit (model := model) spec modulus) := by
  cases instruction with
  | add left right output => exact add _ _ _ _
  | sub left right output => exact sub _ _ _ _
  | multiply left right output => exact multiply _ _ _ _
  | coefficient input output => exact coefficient _ _ _
  | write array index input => exact (LiveSpace.instruction _).mono zero_le

/-- The actual empty branch allocates nothing; every nonempty batch reuses one inverse scope. -/
lemma batch (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    (count : Nat) (fits : count < length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.circuit (model := model) spec count fits) := by
  unfold BatchFrame.circuit
  by_cases empty : count = 0
  · rw [if_pos empty]
    intro path
    rw [Circuit.peakResidentSpace_id, Circuit.peakAuxiliarySpace_id]
    exact ⟨le_add_of_nonneg_left zero_le, le_add_of_nonneg_left zero_le⟩
  · rw [if_neg empty]
    apply seq
    · exact (instruction _).mono zero_le
    · apply seq
      · apply range
        intro index
        apply seq
        · exact (instruction _).mono zero_le
        · exact multiply _ _ _ _
      · apply seq
        · exact coefficient _ _ _
        · apply range
          intro index
          apply seq
          · exact multiply _ _ _ _
          · apply seq
            · exact multiply _ _ _ _
            · exact (instruction _).mono zero_le

variable (frame : TableFrame ctx width length)

private lemma seed_bound (index : Fin length) :
    Bound (coefficientScratchSpace model.kind width) (frame.seedRow (model := model) index) := by
  exact seq _ _ _ ((instruction _).mono zero_le) ((instruction _).mono zero_le)

private lemma double_bound (spec : ModulusSpec width) (source destination : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.doubleRow (model := model) spec source destination) := by
  rw [frame.doubleRow_eq_instructions]
  exact range _ _ _ (fun _ => row_bound _ _ _)

private lemma denominator_bound (seed row : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.denominatorRow (model := model) seed row) := by
  exact seq _ _ _ (sub _ _ _ _) ((instruction _).mono zero_le)

private lemma extend_bound (spec : ModulusSpec width) (seed row destination : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.extendRow (model := model) seed row destination) := by
  rw [frame.extendRow_eq_instructions spec]
  exact range _ _ _ (fun _ => row_bound _ _ _)

private lemma tangent_bound (spec : ModulusSpec width) (row : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.tangentDenominatorRow (model := model) row) := by
  rw [frame.tangentDenominatorRow_eq_instructions spec]
  exact range _ _ _ (fun _ => row_bound _ _ _)

private lemma finish_bound (spec : ModulusSpec width) (row : Fin length) :
    Bound (coefficientScratchSpace model.kind width) (frame.finishRow (model := model) row) := by
  rw [frame.finishRow_eq_instructions spec]
  exact range _ _ _ (fun _ => row_bound _ _ _)

private lemma identity_bound (row : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.clearIdentityRow (model := model) row) := by
  apply range
  intro index
  fin_cases index <;> exact (instruction _).mono zero_le

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

private lemma prepare_bound (spec : ModulusSpec width) (level : Fin window) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.prepareSeed (model := model) spec level) := by
  unfold TableFrame.prepareSeed
  by_cases first : level.val = 0
  · rw [if_pos first]
    exact seed_bound frame _
  · rw [if_neg first]
    exact double_bound frame _ _ _

private lemma layer_bound (spec : ModulusSpec width) (level : Fin window) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.layerCircuit (model := model) spec level) := by
  apply seq
  · exact prepare_bound frame _ _
  · apply seq
    · exact range _ _ _ (fun _ => denominator_bound frame _ _)
    · exact seq _ _ _ (batch frame.batch _ _ _)
        (range _ _ _ (fun _ => extend_bound frame spec _ _ _))

/-- Every actual builder path retains its complete caller and only the shared live scratch. -/
lemma builder (spec : ModulusSpec width) :
    Bound (coefficientScratchSpace model.kind width) (frame.circuit (model := model) spec) := by
  apply seq
  · exact range _ _ _ (fun level => layer_bound frame spec level)
  · apply seq
    · exact range _ _ _ (fun _ => tangent_bound frame spec _)
    · apply seq
      · exact batch frame.batch _ _ _
      · exact seq _ _ _ (range _ _ _ (fun _ => finish_bound frame spec _)) (identity_bound frame _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace
