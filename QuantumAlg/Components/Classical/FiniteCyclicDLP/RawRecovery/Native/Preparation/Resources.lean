/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Decode.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Negate.Resources
import all QuantumAlg.Components.Classical.Word.Split.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Actual preparation traces and serial depth

The original denominator is seeded once by increment and width-many shifts;
its real allocator already supplied zero. Both scaling triples and the
selected two-operation negation are counted on the same actual path. The
finite measurement packing operation is included before the original decoder.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual denominator seeding contains one increment and the original width-many left shifts. -/
def preparationSeedEvents (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (width + 1)))] ++
    Word.PowerOfTwo.shiftTrace (model := model) (width + 1) width

/-- The original seed is not repeated by either frequency scaling. -/
lemma preparationSeed_eventTrace (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (scaleSeed (model := model) denominator).Path) :
    (scaleSeed (model := model) denominator).eventTrace path = preparationSeedEvents model
      width := by
  change (BitWord.instruction (execution := model)
    (Word.PowerOfTwo.incrementOp denominator)).eventTrace path.1 ++
    (Word.PowerOfTwo.shiftInto (model := model) width denominator).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, Word.PowerOfTwo.shiftInto_events]
  rfl

/-- The three final instructions include only the actually selected copy or subtraction. -/
lemma preparationFinalize_eventTrace (refs : PreparationRefs ctx width)
    (path : (preparationFinalize (model := model) refs).Path) :
    (preparationFinalize (model := model) refs).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))] ++
        negateEvents model width path.2.2.1.toBool := by
  change (BitWord.instruction (execution := model) refs.narrowOp).eventTrace path.1 ++
    (negateBody (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
      (scaleRead refs.zero) refs.negationFlag refs.negatedRight).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, negateBody_eventTrace]
  rfl

/-- Every actual preparation path has its original chronological component trace. -/
lemma preparationBody_eventTrace (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody (model := model) spec input
      refs).Path) :
    (preparationBody (model := model) spec input refs).eventTrace path =
      (((measuredDecodeInto (model := model) input refs.decoded).eventTrace path.1.1.1 ++
          Word.Split.splitTrace (model := model) width width) ++
        ((ConstantWord.circuit (model := model) refs.modulusWide spec.modulus).eventTrace
          path.1.2.1 ++
          preparationSeedEvents model width)) ++
        ((scaleBodyEvents (model := model) width ++ scaleBodyEvents (model := model) width) ++
          ([.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))] ++
            negateEvents model width path.2.2.2.2.1.toBool)) := by
  change (((measuredDecodeInto (model := model) input refs.decoded).eventTrace path.1.1.1 ++
      (Word.Split.splitInto (model := model) refs.split).eventTrace path.1.1.2) ++
    ((ConstantWord.circuit (model := model) refs.modulusWide spec.modulus).eventTrace path.1.2.1 ++
      (scaleSeed (model := model) refs.denominator).eventTrace path.1.2.2)) ++
    ((preparationScale (model := model) refs).eventTrace path.2.1 ++
      (preparationFinalize (model := model) refs).eventTrace path.2.2) = _
  have scaled : (preparationScale (model := model) refs).eventTrace path.2.1 =
      scaleBodyEvents (model := model) width ++ scaleBodyEvents (model := model) width :=
    scalePairBody_eventTrace (model := model) (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
      (scaleRead refs.modulusWide) (scaleRead refs.denominator)
      refs.product refs.division refs.left refs.right path.2.1
  rw [Word.Split.splitInto_events, preparationSeed_eventTrace, preparationFinalize_eventTrace,
    scaled]

/-- Seeding depends serially on its increment and each of the original left shifts. -/
lemma preparationSeed_unitDepth (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (scaleSeed (model := model) denominator).Path) :
    (scaleSeed (model := model) denominator).depth (fun _ => 1) path = width + 1 := by
  change 1 + (Word.PowerOfTwo.shiftInto (model := model) width denominator).depth (fun _ => 1)
    path.2 = _
  rw [Word.PowerOfTwo.shiftInto_depth]
  omega

/-- Exactly six dependent native operations execute across the original two scalings. -/
lemma preparationScale_unitDepth (refs : PreparationRefs ctx width)
    (path : (preparationScale (model := model) refs).Path) :
    (preparationScale (model := model) refs).depth (fun _ => 1) path = 6 := rfl

/-- Either actual final branch has one resize, one equality and one arithmetic operation. -/
lemma preparationFinalize_unitDepth (refs : PreparationRefs ctx width)
    (path : (preparationFinalize (model := model) refs).Path) :
    (preparationFinalize (model := model) refs).depth (fun _ => 1) path = 3 := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- The original preparation bound includes the one actual finite-measurement packing operation. -/
lemma preparationBody_unitDepth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody (model := model) spec input
      refs).Path) :
    (preparationBody (model := model) spec input refs).depth (fun _ => 1) path ≤ 8 * width + 15
      := by
  have decoder := measuredDecodeInto_depth_le input refs.decoded (fun _ => 1) path.1.1.1
  have loader := ConstantWord.constantWord_depth_le (model := model) refs.modulusWide spec.modulus
    (fun _ => 1) path.1.2.1
  change (((measuredDecodeInto (model := model) input refs.decoded).depth (fun _ => 1) path.1.1.1 +
      (Word.Split.splitInto (model := model) refs.split).depth (fun _ => 1) path.1.1.2) +
    ((ConstantWord.circuit (model := model) refs.modulusWide spec.modulus).depth (fun _ => 1)
      path.1.2.1 +
      (scaleSeed (model := model) refs.denominator).depth (fun _ => 1) path.1.2.2)) +
    ((preparationScale (model := model) refs).depth (fun _ => 1) path.2.1 +
      (preparationFinalize (model := model) refs).depth (fun _ => 1) path.2.2) ≤ _
  rw [Word.Split.splitInto_depth, preparationSeed_unitDepth, preparationScale_unitDepth,
    preparationFinalize_unitDepth]
  omega

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
