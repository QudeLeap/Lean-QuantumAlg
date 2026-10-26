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

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Resources

/-!
# Paid nearest preparation events and serial depth

Both real seven-operation nearest scalings occur after the existing decoder
and paid loaders. Rounding and canonical wrap add eight actual operations per
attempt. The enclosing preparation retains one extra product-width word.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalAlgorithms.Modular
open RawRecovery.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Every actual preparation path has its original chronological component trace. -/
lemma preparationBody_eventTrace (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationBody (model := model) spec input
      refs half).Path) :
    (preparationBody (model := model) spec input refs half).eventTrace path =
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
    ((preparationScale (model := model) refs half).eventTrace path.2.1 ++
      (preparationFinalize (model := model) refs).eventTrace path.2.2) = _
  have scaled : (preparationScale (model := model) refs half).eventTrace path.2.1 =
      scaleBodyEvents (model := model) width ++ scaleBodyEvents (model := model) width :=
    congrArg₂ List.append
        (scaleBody_eventTrace (scaleRefs refs half false) path.2.1.1)
        (scaleBody_eventTrace (scaleRefs refs half true) path.2.1.2)
  rw [Word.Split.splitInto_events, preparationSeed_eventTrace, preparationFinalize_eventTrace,
    scaled]

/-- The two actual nearest scalings have fourteen serial native instructions. -/
lemma preparationScale_unitDepth (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationScale (model := model) refs half).Path) :
    (preparationScale (model := model) refs half).depth (fun _ => 1) path = 14 := rfl

/-- The original preparation bound includes the one actual finite-measurement packing operation. -/
lemma preparationBody_unitDepth_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (path : (preparationBody (model := model) spec input
      refs half).Path) :
    (preparationBody (model := model) spec input refs half).depth (fun _ => 1) path ≤ 8 * width + 23
      := by
  have decoder := measuredDecodeInto_depth_le input refs.decoded (fun _ => 1) path.1.1.1
  have loader := ConstantWord.constantWord_depth_le (model := model) refs.modulusWide spec.modulus
    (fun _ => 1) path.1.2.1
  change (((measuredDecodeInto (model := model) input refs.decoded).depth (fun _ => 1) path.1.1.1 +
      (Word.Split.splitInto (model := model) refs.split).depth (fun _ => 1) path.1.1.2) +
    ((ConstantWord.circuit (model := model) refs.modulusWide spec.modulus).depth (fun _ => 1)
      path.1.2.1 +
      (scaleSeed (model := model) refs.denominator).depth (fun _ => 1) path.1.2.2)) +
    ((preparationScale (model := model) refs half).depth (fun _ => 1) path.2.1 +
      (preparationFinalize (model := model) refs).depth (fun _ => 1) path.2.2) ≤ _
  rw [Word.Split.splitInto_depth, preparationSeed_unitDepth, preparationScale_unitDepth,
    preparationFinalize_unitDepth]
  omega

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
