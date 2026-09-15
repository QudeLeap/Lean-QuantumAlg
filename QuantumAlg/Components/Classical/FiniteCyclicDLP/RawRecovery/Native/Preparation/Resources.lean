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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual denominator seeding contains one increment and the original width-many left shifts. -/
def preparationSeedEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .increment (width + 1))] ++
    Word.PowerOfTwo.shiftTrace (width + 1) width

/-- The original seed is not repeated by either frequency scaling. -/
theorem preparationSeed_eventTrace (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (scaleSeed denominator).Path) :
    (scaleSeed denominator).eventTrace path = preparationSeedEvents kind width :=
  congrArg (fun trace : List (Resource.Event kind) =>
    ([.classicalOperation (.wordUnary .increment (width + 1))] :
      List (Resource.Event kind)) ++ trace)
    (Word.PowerOfTwo.shiftInto_events width denominator path.2)

/-- The three final instructions include only the actually selected copy or subtraction. -/
theorem preparationFinalize_eventTrace (refs : PreparationRefs ctx width)
    (path : (preparationFinalize refs).Path) :
    (preparationFinalize refs).eventTrace path =
      [.classicalOperation (.wordResize (width + 1) width)] ++
        negateEvents kind width path.2.2.1.toBool := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Every actual preparation path has its original chronological component trace. -/
theorem preparationBody_eventTrace (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody spec input refs).Path) :
    (preparationBody spec input refs).eventTrace path =
      (((measuredDecodeInto input refs.decoded).eventTrace path.1.1.1 ++
          Word.Split.splitTrace width width) ++
        ((ConstantWord.circuit refs.modulusWide spec.modulus).eventTrace path.1.2.1 ++
          preparationSeedEvents kind width)) ++
        ((scaleBodyEvents kind width ++ scaleBodyEvents kind width) ++
          ([.classicalOperation (.wordResize (width + 1) width)] ++
            negateEvents kind width path.2.2.2.2.1.toBool)) := by
  change (((measuredDecodeInto input refs.decoded).eventTrace path.1.1.1 ++
      (Word.Split.splitInto refs.split).eventTrace path.1.1.2) ++
    ((ConstantWord.circuit refs.modulusWide spec.modulus).eventTrace path.1.2.1 ++
      (scaleSeed refs.denominator).eventTrace path.1.2.2)) ++
    ((preparationScale refs).eventTrace path.2.1 ++
      (preparationFinalize refs).eventTrace path.2.2) = _
  rw [Word.Split.splitInto_events, preparationSeed_eventTrace, preparationFinalize_eventTrace]
  rfl

/-- Seeding depends serially on its increment and each of the original left shifts. -/
theorem preparationSeed_unitDepth (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (scaleSeed denominator).Path) :
    (scaleSeed denominator).depth (fun _ => 1) path = width + 1 := by
  change 1 + (Word.PowerOfTwo.shiftInto width denominator).depth (fun _ => 1) path.2 = _
  rw [Word.PowerOfTwo.shiftInto_depth]
  omega

/-- Exactly six dependent native operations execute across the original two scalings. -/
theorem preparationScale_unitDepth (refs : PreparationRefs ctx width)
    (path : (preparationScale refs).Path) :
    (preparationScale refs).depth (fun _ => 1) path = 6 := rfl

/-- Either actual final branch has one resize, one equality and one arithmetic operation. -/
theorem preparationFinalize_unitDepth (refs : PreparationRefs ctx width)
    (path : (preparationFinalize refs).Path) :
    (preparationFinalize refs).depth (fun _ => 1) path = 3 := by
  rcases path with ⟨resizePath, testPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- The original preparation bound includes the one actual finite-measurement packing operation. -/
theorem preparationBody_unitDepth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (path : (preparationBody spec input refs).Path) :
    (preparationBody spec input refs).depth (fun _ => 1) path ≤ 8 * width + 15 := by
  have decoder := measuredDecodeInto_depth_le input refs.decoded (fun _ => 1) path.1.1.1
  have loader := ConstantWord.constantWord_depth_le refs.modulusWide spec.modulus
    (fun _ => 1) path.1.2.1
  change (((measuredDecodeInto input refs.decoded).depth (fun _ => 1) path.1.1.1 +
      (Word.Split.splitInto refs.split).depth (fun _ => 1) path.1.1.2) +
    ((ConstantWord.circuit refs.modulusWide spec.modulus).depth (fun _ => 1) path.1.2.1 +
      (scaleSeed refs.denominator).depth (fun _ => 1) path.1.2.2)) +
    ((preparationScale refs).depth (fun _ => 1) path.2.1 +
      (preparationFinalize refs).depth (fun _ => 1) path.2.2) ≤ _
  rw [Word.Split.splitInto_depth, preparationSeed_unitDepth, preparationScale_unitDepth,
    preparationFinalize_unitDepth]
  omega

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
