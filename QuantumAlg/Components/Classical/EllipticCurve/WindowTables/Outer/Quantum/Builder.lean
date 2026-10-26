/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Arithmetic
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Quantum-event projections of the original complete five-table builder

The actual total batch inverse and every original row instruction are
retained. Their native classical events contribute zero at each separate
quantum gate/measurement coordinate, without a classical-to-gate rate.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]

variable (focus : Resource.Event model)
  (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate)
  {ctx : RuntimeCtx model.kind}

omit [BitWord.Selected model] in
/-- An exact zero coordinate is retained by chronological composition of actual paths. -/
lemma seq_count_zero (first second : Circuit model ctx ctx)
    (path : (first.seq second).Path)
    (left : ResourcePool.count focus (first.resourcePool path.1) = 0)
    (right : ResourcePool.count focus (second.resourcePool path.2) = 0) :
    ResourcePool.count focus ((first.seq second).resourcePool path) = 0 := by
  rw [Circuit.resourcePool_count_seq, left, right, Nat.zero_add]

omit [BitWord.Selected model] in
/-- The actual finite loop has no event at a coordinate absent from each selected component. -/
lemma range_count_zero (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (zero : ∀ index path, ResourcePool.count focus ((body index).resourcePool path) = 0)
    (path : (Circuit.forRange count body).Path) :
    ResourcePool.count focus ((Circuit.forRange count body).resourcePool path) = 0 :=
  (Circuit.forRange_event_count focus count body 0 zero path).trans (Nat.mul_zero _)

variable {width length : Nat}

include model nativeFree

/-- The actual complete prefix/inverse/reverse batch contributes no quantum event. -/
lemma batch_count_zero (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    (count : Nat) (fits : count < length)
    : ∀ path : (frame.circuit (model := model) spec count fits).Path,
    ResourcePool.count focus ((frame.circuit (model := model) spec count fits).resourcePool path) =
      0 := by
  unfold BatchFrame.circuit
  by_cases empty : count = 0
  · rw [if_pos empty]
    intro path
    change ResourcePool.count focus 0 = 0
    exact ResourcePool.count_zero focus
  · rw [if_neg empty]
    intro path
    apply seq_count_zero focus
    · exact instruction_count_zero focus nativeFree _ _
    · apply seq_count_zero focus
      · apply range_count_zero focus
        intro index selected
        apply seq_count_zero focus
        · exact instruction_count_zero focus nativeFree _ _
        · exact multiply_count_zero focus nativeFree _ _ _ _ _
      · apply seq_count_zero focus
        · exact coefficient_count_zero focus nativeFree _ _ _ _
        · apply range_count_zero focus
          intro index selected
          apply seq_count_zero focus
          · exact multiply_count_zero focus nativeFree _ _ _ _ _
          · apply seq_count_zero focus
            · exact multiply_count_zero focus nativeFree _ _ _ _ _
            · exact instruction_count_zero focus nativeFree _ _

variable (frame : TableFrame ctx width length)

private lemma seed_count_zero (index : Fin length)
    (path : (frame.seedRow (model := model) index).Path) :
    ResourcePool.count focus ((frame.seedRow (model := model) index).resourcePool path) = 0 := by
  exact seq_count_zero focus _ _ path
    (instruction_count_zero focus nativeFree _ _) (instruction_count_zero focus nativeFree _ _)

private lemma row_count_zero (instruction : RowInstruction ctx width length)
    (spec : ModulusSpec width) (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (instruction.circuit (model := model) spec modulus).Path) :
    ResourcePool.count focus ((instruction.circuit spec modulus).resourcePool path) = 0 := by
  cases instruction with
  | add left right output => exact add_count_zero focus nativeFree _ _ _ _ _
  | sub left right output => exact sub_count_zero focus nativeFree _ _ _ _ _
  | multiply left right output => exact multiply_count_zero focus nativeFree _ _ _ _ _
  | coefficient input output => exact coefficient_count_zero focus nativeFree _ _ _ _
  | write array index input => exact instruction_count_zero focus nativeFree _ _

private lemma double_count_zero (spec : ModulusSpec width) (source destination : Fin length)
    : ∀ path : (frame.doubleRow (model := model) spec source destination).Path,
    ResourcePool.count focus
      ((frame.doubleRow (model := model) spec source destination).resourcePool path) = 0 := by
  rw [frame.doubleRow_eq_instructions]
  intro path
  exact range_count_zero focus _ _ (fun _ => row_count_zero focus nativeFree _ _ _) path

private lemma denominator_count_zero (seed row : Fin length)
    (path : (frame.denominatorRow (model := model) seed row).Path) :
    ResourcePool.count focus
      ((frame.denominatorRow (model := model) seed row).resourcePool path) = 0 := by
  exact seq_count_zero focus _ _ path
    (sub_count_zero focus nativeFree _ _ _ _ _) (instruction_count_zero focus nativeFree _ _)

private lemma extend_count_zero (spec : ModulusSpec width) (seed row destination : Fin length)
    : ∀ path : (frame.extendRow (model := model) seed row destination).Path,
    ResourcePool.count focus
      ((frame.extendRow (model := model) seed row destination).resourcePool path) = 0 := by
  rw [frame.extendRow_eq_instructions spec]
  intro path
  exact range_count_zero focus _ _ (fun _ => row_count_zero focus nativeFree _ _ _) path

private lemma tangent_count_zero (spec : ModulusSpec width) (row : Fin length)
    : ∀ path : (frame.tangentDenominatorRow (model := model) row).Path,
    ResourcePool.count focus
      ((frame.tangentDenominatorRow (model := model) row).resourcePool path) = 0 := by
  rw [frame.tangentDenominatorRow_eq_instructions spec]
  intro path
  exact range_count_zero focus _ _ (fun _ => row_count_zero focus nativeFree _ _ _) path

private lemma finish_count_zero (spec : ModulusSpec width) (row : Fin length)
    : ∀ path : (frame.finishRow (model := model) row).Path,
    ResourcePool.count focus ((frame.finishRow (model := model) row).resourcePool path) = 0 := by
  rw [frame.finishRow_eq_instructions spec]
  intro path
  exact range_count_zero focus _ _ (fun _ => row_count_zero focus nativeFree _ _ _) path

private lemma identity_count_zero (row : Fin length)
    (path : (frame.clearIdentityRow (model := model) row).Path) :
    ResourcePool.count focus
      ((frame.clearIdentityRow (model := model) row).resourcePool path) = 0 := by
  apply range_count_zero focus
  intro index selected
  fin_cases index <;> exact instruction_count_zero focus nativeFree _ _

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

private lemma prepare_count_zero (spec : ModulusSpec width) (level : Fin window) :
    ∀ path : (frame.prepareSeed (model := model) spec level).Path,
    ResourcePool.count focus ((frame.prepareSeed (model := model) spec level).resourcePool path) =
      0 := by
  unfold TableFrame.prepareSeed
  by_cases first : level.val = 0
  · rw [if_pos first]
    exact seed_count_zero focus nativeFree frame _
  · rw [if_neg first]
    exact double_count_zero focus nativeFree frame _ _ _

private lemma layer_count_zero (spec : ModulusSpec width) (level : Fin window)
    (path : (frame.layerCircuit (model := model) spec level).Path) :
    ResourcePool.count focus ((frame.layerCircuit (model := model) spec level).resourcePool path) =
      0 := by
  apply seq_count_zero focus
  · exact prepare_count_zero focus nativeFree frame _ _ _
  · apply seq_count_zero focus
    · apply range_count_zero focus
      intro index selected
      exact denominator_count_zero focus nativeFree frame _ _ selected
    · apply seq_count_zero focus
      · exact batch_count_zero focus nativeFree frame.batch _ _ _ _
      · apply range_count_zero focus
        intro index selected
        exact extend_count_zero focus nativeFree frame spec _ _ _ selected

/-- Every actual full-builder path is exactly zero at each nonclassical event coordinate. -/
lemma builder_count_zero (spec : ModulusSpec width)
    (path : (frame.circuit (model := model) spec).Path) :
    ResourcePool.count focus ((frame.circuit (model := model) spec).resourcePool path) = 0 := by
  apply seq_count_zero focus
  · apply range_count_zero focus
    intro level selected
    exact layer_count_zero focus nativeFree frame spec level selected
  · apply seq_count_zero focus
    · apply range_count_zero focus
      intro index selected
      exact tangent_count_zero focus nativeFree frame spec _ selected
    · apply seq_count_zero focus
      · exact batch_count_zero focus nativeFree frame.batch _ _ _ _
      · apply seq_count_zero focus
        · apply range_count_zero focus
          intro index selected
          exact finish_count_zero focus nativeFree frame spec _ selected
        · exact identity_count_zero focus nativeFree frame _ _

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting
