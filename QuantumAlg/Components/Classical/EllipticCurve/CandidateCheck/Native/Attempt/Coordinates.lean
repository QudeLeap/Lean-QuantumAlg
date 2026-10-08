/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Depth

/-!
# Classical coordinates of the original complete attempt allowance

The original raw recovery, field arithmetic, complete point operations and
first-success selector contain only native classical-operation labels.
This fact is proved on their unchanged independent envelopes, including each
actual branch maximum and constant-loader trace. It introduces no execution
restriction and no replacement instruction or cost model.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open NumberTheory.XGCD.Native NumberTheory.Checked.Native
open NumberTheory.Checked.SignedReduction.Native
open FiniteCyclicDLP.RawRecovery.Native Field.Native Add.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] (event : Resource.Event model)
    (outside : ∀ label, event ≠ .classicalOperation label)

include outside

private theorem loader_zero (width : Nat) (bits : List Bool) :
    ResourcePool.count event (ResourcePool.ofList (ConstantWord.loaderTrace model width bits)) =
      0 := by
  induction bits with
  | nil => simp [ConstantWord.loaderTrace, ResourcePool.ofList, ResourcePool.count]
  | cons bit rest _ih =>
      cases bit <;>
        simp [ConstantWord.loaderTrace, ConstantWord.shiftEvent, ConstantWord.incrementEvent,
          ResourcePool.ofList, ResourcePool.count, outside]

private theorem raw_zero (width : Nat) :
    ResourcePool.count event (rawEnvelope model width) = 0 := by
  simp [rawEnvelope, initializationEvents, activeEvents,
    NumberTheory.XGCD.coefficientUpdateEvents, rawOutputEvents,
    ResourcePool.ofList, ResourcePool.count, ResourcePool.scale, outside, eq_comm]

private theorem signed_zero (width : Nat) :
    ResourcePool.count event (signedReductionEnvelope model width) = 0 := by
  simp only [signedReductionEnvelope, ResourcePool.count_add, ResourcePool.count_max]
  simp [signClassificationEvents, signedMagnitudeEvents, finalCorrectionEvents,
    negativeCorrectionEvents, Modular.Reduce.Native.reductionEvents,
    ResourcePool.ofList, ResourcePool.count, outside]

private theorem coefficient_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (coefficientEnvelope model spec) = 0 := by
  simp only [coefficientEnvelope, ResourcePool.count_add,
    loader_zero event outside, raw_zero event outside, signed_zero event outside]
  simp [ResourcePool.ofList, ResourcePool.count, outside]

private theorem reduction_zero {width : Nat} (spec : ModulusSpec width) (sourceWidth : Nat) :
    ResourcePool.count event
      (ResourcePool.ofList (loadedReductionTrace model sourceWidth spec)) = 0 := by
  simp only [loadedReductionTrace, ResourcePool.ofList_append, ResourcePool.count_add,
    loader_zero event outside]
  simp [Modular.Reduce.Native.reductionEvents, ResourcePool.ofList, ResourcePool.count,
    outside]

private theorem product_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (ResourcePool.ofList (multiplicationTrace model spec)) = 0 := by
  simpa [multiplicationTrace, ResourcePool.ofList, ResourcePool.count, outside, eq_comm] using
    reduction_zero event outside spec (width + width)

private theorem addition_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (ResourcePool.ofList (additionTrace model spec)) = 0 := by
  simp only [additionTrace, ResourcePool.ofList_append, ResourcePool.count_add,
    reduction_zero event outside]
  simp [additionPrefixTrace, ResourcePool.ofList, ResourcePool.count, outside]

private theorem subtraction_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (ResourcePool.ofList (subtractionTrace model spec)) = 0 := by
  simp only [subtractionTrace, subtractionPrefixTrace, ResourcePool.ofList_append,
    ResourcePool.count_add, reduction_zero event outside, loader_zero event outside]
  simp [ResourcePool.ofList, ResourcePool.count, outside]

private theorem affine_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (affineEnvelope model spec) = 0 := by
  simp only [affineEnvelope, affineStageEnvelope, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, ResourcePool.count_add,
    coefficient_zero event outside, product_zero event outside, subtraction_zero event outside]
  simp [ResourcePool.ofList, ResourcePool.count, outside]

private theorem generic_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (genericEnvelope model spec) = 0 := by
  simp only [genericEnvelope, ResourcePool.count_add, subtraction_zero event outside,
    affine_zero event outside, add_zero]

private theorem doubling_zero {width : Nat} (spec : CurveSpec width) :
    ResourcePool.count event (doublingEnvelope model spec) = 0 := by
  simp only [doublingEnvelope, doublingStageEnvelope, doublingLoaderTrace,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, ResourcePool.count_add, product_zero event outside, addition_zero event outside,
    loader_zero event outside, affine_zero event outside]

private theorem complete_zero {width : Nat} (spec : CurveSpec width) :
    ResourcePool.count event (additionEnvelope model spec) = 0 := by
  simp only [additionEnvelope, additionBranchEnvelope, caseMaximum, additionArmEnvelope,
    ResourcePool.count_add, ResourcePool.count_max, generic_zero event outside,
    doubling_zero event outside]
  simp [classifierTrace, infinityTrace, ResourcePool.ofList, ResourcePool.count, outside]

private theorem scalar_zero {width : Nat} (spec : CurveSpec width) (count : Nat) :
    ResourcePool.count event (ScalarMul.Native.scalarEnvelope model spec count) = 0 := by
  simp only [ScalarMul.Native.scalarEnvelope, ResourcePool.count_add, ResourcePool.count_scale,
    complete_zero event outside, add_zero, mul_zero]
  simp [infinityTrace, ResourcePool.ofList, ResourcePool.count, outside]

private theorem verification_zero {width : Nat} (spec : CurveSpec width) (count : Nat) :
    ResourcePool.count event (verificationEnvelope model spec count) = 0 := by
  simp only [verificationEnvelope, verificationStageEnvelope, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    ResourcePool.count_add, scalar_zero event outside]
  simp [PointEquality.coreEnvelope, PointEquality.coreTrace,
    ResourcePool.ofList, ResourcePool.count, outside]

private theorem checked_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (checkedInverseEnvelope model spec) = 0 := by
  simp only [checkedInverseEnvelope, checkedSelectionEnvelope, ResourcePool.count_add,
    ResourcePool.count_max, loader_zero event outside, raw_zero event outside,
    signed_zero event outside]
  simp [checkedDecisionEvents, ResourcePool.ofList, ResourcePool.count, outside]

private theorem preparation_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (preparationEnvelope model spec) = 0 := by
  simp only [preparationEnvelope, preparationFinalEnvelope, measuredDecodeEnvelope,
    TerminalDecode.envelope, TerminalDecode.bitEnvelope, ResourcePool.count_add,
    ResourcePool.count_scale, ResourcePool.count_max, loader_zero event outside]
  simp [measuredPackEvent, TerminalDecode.shiftEvent, TerminalDecode.incrementEvent,
    Word.Split.splitTrace, Word.Split.shiftTrace, preparationSeedEvents, Word.PowerOfTwo.shiftTrace,
    scaleBodyEvents, negateEvents, ResourcePool.singleton, ResourcePool.ofList,
    ResourcePool.count, outside]

private theorem exposure_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (singleExposureEnvelope model spec) = 0 := by
  simp only [singleExposureEnvelope, checkedExposureEnvelope, ResourcePool.count_add,
    preparation_zero event outside, checked_zero event outside]
  simp [selectedExposureEvents, exposureCopyEvents,
    FiniteCyclicDLP.NormalizedRecovery.Native.recoveryEvents,
    ResourcePool.ofList, ResourcePool.count, outside]

/-- No non-classical-operation coordinate occurs in the original complete attempt allowance. -/
theorem attemptEnvelope_count_eq_zero {width scalarWidth : Nat}
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth) :
    ResourcePool.count event (attemptEnvelope model curve modulus) = 0 := by
  simp only [attemptEnvelope, ResourcePool.count_add, exposure_zero event outside,
    verification_zero event outside]
  simp [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    ResourcePool.ofList, ResourcePool.count, outside]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
