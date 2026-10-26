/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Builder
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Actual preparation peaks with the same four scalar words

Constant loading uses existing cells. Both original seventeen-row base
families reuse the original scalar scratch between every actual doubling.
Their resident and auxiliary peaks retain every original caller role.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

private lemma constant_bound (output : CWriteRef ctx (.unsignedWord width)) (constant : Nat) :
    Bound 0 (ConstantWord.circuit (model := model) output constant) := by
  intro path
  simpa only [zero_add] using And.intro
    (ConstantWord.constantWord_resident_le output constant path)
    (ConstantWord.constantWord_auxiliary_le output constant path)

private lemma slot_bound (instruction : RowInstruction ctx width length)
    (spec : ModulusSpec width) (modulus : CWriteRef ctx (.unsignedWord (width + 1))) :
    Bound (coefficientScratchSpace model.kind width)
      (instruction.circuit (model := model) spec modulus) := by
  cases instruction with
  | add left right output => exact add _ _ _ _
  | sub left right output => exact sub _ _ _ _
  | multiply left right output => exact multiply _ _ _ _
  | coefficient input output => exact coefficient _ _ _
  | write array index input => exact (LiveSpace.instruction _).mono zero_le

private lemma coordinateDouble_bound (frame : CoordinateFrame ctx width length)
    (spec : ModulusSpec width) (source destination : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.doubleCircuit (model := model) spec source destination) := by
  exact range _ _ _ (fun _ => slot_bound _ _ _)

private lemma baseStep_bound (frame : CoordinateFrame ctx width length)
    (spec : ModulusSpec width) (source destination : Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.baseStep (model := model) spec source destination) := by
  exact seq _ _ _ (coordinateDouble_bound frame _ _ _)
    (range _ _ _ (fun _ => coordinateDouble_bound frame _ _ _))

private lemma bases_bound {baseCount : Nat} (frame : CoordinateFrame ctx width length)
    (spec : ModulusSpec width) (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.prepareBasesAt (model := model) spec sourceX sourceY rows) := by
  exact seq _ _ _
    (seq _ _ _ ((instruction _).mono zero_le) ((instruction _).mono zero_le))
    (range _ _ _ (fun _ => baseStep_bound frame _ _ _))

/-- Actual constants need no cell beyond the original shared package. -/
lemma initialization (frame : Frame ctx width) (spec : ModulusSpec width) (coefficient : Nat) :
    Bound 0 (frame.initializeConstants (model := model) spec coefficient) := by
  exact seq _ _ _ (constant_bound _ _)
    (seq _ _ _ (constant_bound _ _) (instruction _))

/-- Both actual small-base preparations reuse the same original arithmetic scratch. -/
lemma pairedBases (frame : Frame ctx width) (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width)) :
    Bound (coefficientScratchSpace model.kind width)
      (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY) := by
  exact seq _ _ _ (bases_bound frame.coordinates _ _ _ _)
    (bases_bound frame.coordinates _ _ _ _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace
