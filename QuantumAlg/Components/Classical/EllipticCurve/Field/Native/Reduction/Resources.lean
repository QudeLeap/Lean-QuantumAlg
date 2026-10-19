/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Reduction
import all QuantumAlg.Components.Classical.ConstantWord.Trace
import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Resources

/-!
# Actual modulus-loading and raw-reduction resources

Every original modulus shift and selected increment is counted before the
original division and resize. The actual simultaneous modulus and division
pair give the exact live-space peak, including the whole caller context.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalAlgorithms.Modular
open Modular.Reduce.Native

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {sourceWidth width : Nat}

/-- Exact original MSB-first modulus loading followed by the two native reduction events. -/
def loadedReductionTrace (model : ExecutionModel) [BitWord.Selected model]
    (sourceWidth : Nat) (spec : ModulusSpec width) : List (Resource.Event model) :=
  ConstantWord.loaderTrace model (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) ++
      reductionEvents model sourceWidth width

/-- Actual modulus allocation and release retain precisely the original native event trace. -/
lemma fieldReduceIntoWord_eventTrace (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceIntoWord (model := model) spec numerator output).Path) :
    (reduceIntoWord (model := model) spec numerator output).eventTrace path =
      loadedReductionTrace model sourceWidth spec := by
  change (ConstantWord.circuit _ spec.modulus).eventTrace path.1 ++
    (reduceWord _ _ _).eventTrace path.2 = _
  exact congrArg₂ List.append
    (ConstantWord.constantFold_eventTrace (loadedModulusCell ctx width) _ path.1)
    (reduceWord_eventTrace (underLoadedReduction numerator width)
      (reductionRead (loadedModulusCell ctx width)) (writeUnderLoadedReduction output width) path.2)

/-- Counts are derived from the same original actual modulus and reduction events. -/
lemma reduceIntoWord_resourcePool (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceIntoWord (model := model) spec numerator output).Path) :
    (reduceIntoWord (model := model) spec numerator output).resourcePool path =
      ResourcePool.ofList (loadedReductionTrace model sourceWidth spec) :=
  congrArg ResourcePool.ofList (fieldReduceIntoWord_eventTrace spec numerator output path)

/-- Arbitrary durations retain the exact original serial dependency depth. -/
lemma reduceIntoWord_durationDepth (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (reduceIntoWord (model := model) spec numerator output).Path) :
    (reduceIntoWord (model := model) spec numerator output).depth duration path =
      ((loadedReductionTrace model sourceWidth spec).map duration).sum := by
  change (ConstantWord.circuit _ spec.modulus).depth duration path.1 +
    (reduceWord _ _ _).depth duration path.2 = _
  refine (congrArg₂ Nat.add
    (ConstantWord.constantFold_depth (loadedModulusCell ctx width) _ duration path.1)
    (reduceWord_durationDepth (underLoadedReduction numerator width)
      (reductionRead (loadedModulusCell ctx width))
      (writeUnderLoadedReduction output width) duration path.2)).trans ?_
  simp only [loadedReductionTrace, reductionEvents, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

/-- Both actual scratch scopes contribute to the exact resident peak. -/
lemma reduceIntoWord_resident (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceIntoWord (model := model) spec numerator output).Path) :
    (reduceIntoWord (model := model) spec numerator output).peakResidentSpace path =
      SpacePool.ofShape (.unsignedWord (width + 1)) +
        SpacePool.ofShape (divisionShape sourceWidth width) + ctx.residentSpace := by
  have bodyPeak :
      (loadedReductionPlaced (model := model) spec numerator output).peakResidentSpace path =
      SpacePool.ofShape (divisionShape sourceWidth width) +
        (loadedReductionCtx ctx width).residentSpace := by
    refine (Circuit.peakResidentSpace_seq (ConstantWord.circuit (loadedModulusCell ctx width)
      spec.modulus) (reduceWord (underLoadedReduction numerator width)
        (reductionRead (loadedModulusCell ctx width))
        (writeUnderLoadedReduction output width)) path).trans ?_
    rw [reduceWord_resident]
    exact SpacePool.max_eq_right
      ((ConstantWord.constantWord_resident_le _ _ path.1).trans le_add_self)
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (loadedReductionPlaced spec numerator output) path).trans
      ((congrArg (SpacePool.max ctx.residentSpace) bodyPeak).trans ?_)
  have enlarged : ctx.residentSpace ≤ SpacePool.ofShape (divisionShape sourceWidth width) +
      (loadedReductionCtx ctx width).residentSpace := le_trans le_add_self le_add_self
  rw [SpacePool.max_eq_right enlarged]
  change _ + (_ + ctx.residentSpace) = _
  ac_rfl

/-- Both actual scratch scopes have their real auxiliary roles and the same exact peak. -/
lemma reduceIntoWord_auxiliary (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceIntoWord (model := model) spec numerator output).Path) :
    (reduceIntoWord (model := model) spec numerator output).peakAuxiliarySpace path =
      SpacePool.ofShape (.unsignedWord (width + 1)) +
        SpacePool.ofShape (divisionShape sourceWidth width) + ctx.auxiliarySpace := by
  have bodyPeak :
      (loadedReductionPlaced (model := model) spec numerator output).peakAuxiliarySpace path =
      SpacePool.ofShape (divisionShape sourceWidth width) +
        (loadedReductionCtx ctx width).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq (ConstantWord.circuit (loadedModulusCell ctx width)
      spec.modulus) (reduceWord (underLoadedReduction numerator width)
        (reductionRead (loadedModulusCell ctx width))
        (writeUnderLoadedReduction output width)) path).trans ?_
    rw [reduceWord_auxiliary]
    exact SpacePool.max_eq_right
      ((ConstantWord.constantWord_auxiliary_le _ _ path.1).trans le_add_self)
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (loadedReductionPlaced spec numerator output) path).trans
      ((congrArg (SpacePool.max ctx.auxiliarySpace) bodyPeak).trans ?_)
  have enlarged : ctx.auxiliarySpace ≤ SpacePool.ofShape (divisionShape sourceWidth width) +
      (loadedReductionCtx ctx width).auxiliarySpace := le_trans le_add_self le_add_self
  rw [SpacePool.max_eq_right enlarged]
  change _ + (_ + ctx.auxiliarySpace) = _
  ac_rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
