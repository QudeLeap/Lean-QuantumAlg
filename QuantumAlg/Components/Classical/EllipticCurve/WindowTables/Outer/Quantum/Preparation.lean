/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Builder
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Actual small-base and constant preparations add no quantum event

The original two coordinate families retain all paid native doubling and
coefficient calls. Their quantum coordinates are zero because those actual
programs contain only native classical operations.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]

variable (focus : Resource.Event model)
  (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate)
  {ctx : RuntimeCtx model.kind} {width length : Nat}

include model nativeFree

private lemma constant_count_zero (output : CWriteRef ctx (.unsignedWord width)) (constant : Nat)
    (path : (ConstantWord.circuit (model := model) output constant).Path) :
    ResourcePool.count focus
      ((ConstantWord.circuit (model := model) output constant).resourcePool path) = 0 := by
  have actual := Multiset.count_le_of_le focus
    (ConstantWord.constantWord_pool_le output constant path)
  have allowance : ResourcePool.count focus (ConstantWord.envelope model width) = 0 := by
    simp [ConstantWord.envelope, ConstantWord.bitEnvelope, ConstantWord.shiftEvent,
      ConstantWord.incrementEvent, fun coordinate => (nativeFree coordinate).symm]
  change Multiset.count focus (ConstantWord.envelope model width) = 0 at allowance
  change Multiset.count focus ((ConstantWord.circuit output constant).resourcePool path) = 0
  exact Nat.eq_zero_of_le_zero (actual.trans_eq allowance)

private lemma instructionSlot_count_zero (instruction : RowInstruction ctx width length)
    (spec : ModulusSpec width) (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (instruction.circuit (model := model) spec modulus).Path) :
    ResourcePool.count focus
      ((instruction.circuit (model := model) spec modulus).resourcePool path) = 0 := by
  cases instruction with
  | add => exact add_count_zero focus nativeFree _ _ _ _ _
  | sub => exact sub_count_zero focus nativeFree _ _ _ _ _
  | multiply => exact multiply_count_zero focus nativeFree _ _ _ _ _
  | coefficient => exact coefficient_count_zero focus nativeFree _ _ _ _
  | write => exact instruction_count_zero focus nativeFree _ _

private lemma coordinateDouble_count_zero (frame : CoordinateFrame ctx width length)
    (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.doubleCircuit (model := model) spec source destination).Path) :
    ResourcePool.count focus
      ((frame.doubleCircuit (model := model) spec source destination).resourcePool path) = 0 := by
  apply range_count_zero focus
  intro index selected
  exact instructionSlot_count_zero focus nativeFree _ _ _ selected

private lemma baseStep_count_zero (frame : CoordinateFrame ctx width length)
    (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.baseStep (model := model) spec source destination).Path) :
    ResourcePool.count focus
      ((frame.baseStep (model := model) spec source destination).resourcePool path) = 0 := by
  apply seq_count_zero focus
  · exact coordinateDouble_count_zero focus nativeFree frame _ _ _ _
  · apply range_count_zero focus
    intro index selected
    exact coordinateDouble_count_zero focus nativeFree frame _ _ _ selected

private lemma bases_count_zero {baseCount : Nat} (frame : CoordinateFrame ctx width length)
    (spec : ModulusSpec width) (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length)
    (path : (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).Path) :
    ResourcePool.count focus
      ((frame.prepareBasesAt (model := model) spec sourceX sourceY rows).resourcePool path) =
        0 := by
  apply seq_count_zero focus
  · exact seq_count_zero focus _ _ _
      (instruction_count_zero focus nativeFree _ _) (instruction_count_zero focus nativeFree _ _)
  · apply range_count_zero focus
    intro index selected
    exact baseStep_count_zero focus nativeFree frame _ _ _ selected

/-- All actual public constant loading is separate from every quantum event coordinate. -/
lemma initialization_count_zero (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat)
    (path : (frame.initializeConstants (model := model) spec coefficient).Path) :
    ResourcePool.count focus
      ((frame.initializeConstants (model := model) spec coefficient).resourcePool path) = 0 := by
  apply seq_count_zero focus
  · exact constant_count_zero focus nativeFree _ _ _
  · exact seq_count_zero focus _ _ _ (constant_count_zero focus nativeFree _ _ _)
      (instruction_count_zero focus nativeFree _ _)

/-- Both actual seventeen-row base families add zero quantum gates or physical measurements. -/
lemma pairedBases_count_zero (frame : Frame ctx width) (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (path : (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).Path) :
    ResourcePool.count focus
      ((frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).resourcePool
        path) = 0 := by
  exact seq_count_zero focus _ _ path
    (bases_count_zero focus nativeFree frame.coordinates _ _ _ _ _)
    (bases_count_zero focus nativeFree frame.coordinates _ _ _ _ _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting
