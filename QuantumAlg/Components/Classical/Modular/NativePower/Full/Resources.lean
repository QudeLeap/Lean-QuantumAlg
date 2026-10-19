/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Construction
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Depth
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Independent complete native modular-power resource budget

The budget includes actual nominal base unpacking, the extended modulus's
literal shift/increment loader, initialization of the real accumulator, every
selected square-and-multiply, and the final result copy. No modulus loading,
nominal conversion or branch-selected arithmetic is treated as a free read.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

/-- Width-only native allowance including every actual initialization and output instruction. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (width exponentWidth : Nat) :
    ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.residueEncoding .unpack width))) +
    (ConstantWord.envelope model (width + 1) +
      (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width))) +
        (exponentEnvelope model width exponentWidth +
          ResourcePool.singleton (.classicalOperation
            (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width))))))

/-- Independent duration bound of loading, initialization, exponent slots and final copy. -/
def depthBound (width exponentWidth : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.residueEncoding .unpack width))) +
    (width + 1) * (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft (width + 1)))) +
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (width + 1))))) +
    duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width))) +
    exponentWidth * (2 * multiplyDepth width duration) +
    duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)))

/-- Every actual body path fits the independent complete native-coordinate allowance. -/
lemma nativePower_body_pool_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (powerBody (model := model) spec base exponent output).Path) :
    (powerBody (model := model) spec base exponent output).resourcePool path ≤
      eventEnvelope model width exponentWidth := by
  simp only [Circuit.resourcePool, powerBody, Circuit.eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList
    ([.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.residueEncoding .unpack width))] ++
      ((ConstantWord.circuit (model := model) (modulusCell ctx width) spec.modulus).eventTrace
        path.2.1 ++
        ([.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width))] ++
          ((exponentCircuit (model := model) (wordRead (baseCell ctx width))
            (underPower exponent width)
            (wordRead (modulusCell ctx width)) (accumulatorCell ctx width)).eventTrace
              path.2.2.2.1 ++
            [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width))])))) ≤ _
  simp only [ResourcePool.ofList_append, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    add_zero, eventEnvelope]
  exact add_le_add le_rfl
    (add_le_add (ConstantWord.constantWord_pool_le (modulusCell ctx width) spec.modulus path.2.1)
      (add_le_add le_rfl
        (add_le_add (nativePower_exponent_pool_le (wordRead (baseCell ctx width))
          (underPower exponent width) (wordRead (modulusCell ctx width))
          (accumulatorCell ctx width) path.2.2.2.1) le_rfl)))

/-- All lexical allocation and release paths obey that same actual complete event allowance. -/
lemma nativePower_into_pool_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) spec base exponent output).Path) :
    (into (model := model) spec base exponent output).resourcePool path ≤
      eventEnvelope model width exponentWidth :=
  nativePower_body_pool_le spec base exponent output path

/-- The actual body preserves every dependency charged by the complete duration budget. -/
lemma nativePower_body_depth_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (powerBody (model := model) spec base exponent output).Path) :
    (powerBody (model := model) spec base exponent output).depth duration path ≤
      depthBound width exponentWidth duration := by
  rcases path with ⟨unpackPath, loadPath, initializePath, powerPath, copyPath⟩
  have loaded : (ConstantWord.circuit (model := model) (modulusCell ctx width) spec.modulus).depth
      duration loadPath ≤
      (width + 1) * (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft (width + 1)))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (width + 1))))) :=
    ConstantWord.constantWord_depth_le (modulusCell ctx width) spec.modulus duration loadPath
  have powered := nativePower_exponent_depth_le (wordRead (baseCell ctx width))
    (underPower exponent width) (wordRead (modulusCell ctx width)) (accumulatorCell ctx width)
    duration powerPath
  simp only [powerBody, Circuit.depth_seq, BitWord.bitWord_instruction_depth]
  change duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.residueEncoding .unpack width))) +
    ((ConstantWord.circuit (model := model) (modulusCell ctx width) spec.modulus).depth
        duration loadPath +
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width))) +
        ((exponentCircuit (model := model) (wordRead (baseCell ctx width))
            (underPower exponent width)
          (wordRead (modulusCell ctx width)) (accumulatorCell ctx width)).depth
          duration powerPath + duration (.classicalOperation
            (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)))))) ≤ _
  unfold depthBound
  omega

/-- The complete three-scope execution satisfies the independent duration bound. -/
lemma nativePower_into_depth_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (into (model := model) spec base exponent output).Path) :
    (into (model := model) spec base exponent output).depth duration path ≤
      depthBound width exponentWidth duration :=
  nativePower_body_depth_le spec base exponent output duration path

/-- Actual unit depth includes every setup operation and at most six steps per exponent bit. -/
lemma nativePower_into_unitDepth_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) spec base exponent output).Path) :
    (into (model := model) spec base exponent output).depth (fun _ => 1) path ≤
      2 * width + 5 + 6 * exponentWidth := by
  have actual := nativePower_into_depth_le spec base exponent output (fun _ => 1) path
  simp only [depthBound, multiplyDepth] at actual
  omega

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
