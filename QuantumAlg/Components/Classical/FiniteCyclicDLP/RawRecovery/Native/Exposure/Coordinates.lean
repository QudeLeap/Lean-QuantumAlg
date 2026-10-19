/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources

/-!
# Event kinds of raw finite-cyclic recovery

The raw recovery allowance is made entirely from native classical operations.
This structural fact lets algorithm endpoints keep quantum gates and declared
queries in separate public coordinates.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open ClassicalAlgorithms.Modular
open NumberTheory.XGCD.Native NumberTheory.Checked.Native
open NumberTheory.Checked.SignedReduction.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    (event : Resource.Event model)
    (outside : ∀ label, event ≠ .classicalOperation label)

include outside

private lemma loader_count_zero (width : Nat) (bits : List Bool) :
    ResourcePool.count event
      (ResourcePool.ofList (ConstantWord.loaderTrace model width bits)) = 0 := by
  induction bits with
  | nil => simp [ConstantWord.loaderTrace, ResourcePool.ofList, ResourcePool.count]
  | cons bit rest _ih =>
      cases bit <;>
        simp [ConstantWord.loaderTrace, ConstantWord.shiftEvent, ConstantWord.incrementEvent,
          ResourcePool.ofList, ResourcePool.count, outside]

private lemma xgcd_count_zero (width : Nat) :
    ResourcePool.count event (rawEnvelope model width) = 0 := by
  simp [rawEnvelope, initializationEvents, activeEvents,
    NumberTheory.XGCD.coefficientUpdateEvents, rawOutputEvents,
    ResourcePool.ofList, ResourcePool.count, ResourcePool.scale, outside, eq_comm]

private lemma signedReduction_count_zero (width : Nat) :
    ResourcePool.count event (signedReductionEnvelope model width) = 0 := by
  simp only [signedReductionEnvelope, ResourcePool.count_add, ResourcePool.count_max]
  simp [signClassificationEvents, signedMagnitudeEvents, finalCorrectionEvents,
    negativeCorrectionEvents, Modular.Reduce.Native.reductionEvents,
    ResourcePool.ofList, ResourcePool.count, outside]

private lemma checkedInverse_count_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (checkedInverseEnvelope model spec) = 0 := by
  simp only [checkedInverseEnvelope, checkedSelectionEnvelope, ResourcePool.count_add,
    ResourcePool.count_max, loader_count_zero event outside,
    xgcd_count_zero event outside, signedReduction_count_zero event outside]
  simp [checkedDecisionEvents, ResourcePool.ofList, ResourcePool.count, outside]

private lemma preparation_count_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count event (preparationEnvelope model spec) = 0 := by
  simp only [preparationEnvelope, preparationFinalEnvelope, measuredDecodeEnvelope,
    TerminalDecode.envelope, TerminalDecode.bitEnvelope, ResourcePool.count_add,
    ResourcePool.count_scale, ResourcePool.count_max, loader_count_zero event outside]
  simp [measuredPackEvent, TerminalDecode.shiftEvent, TerminalDecode.incrementEvent,
    Word.Split.splitTrace, Word.Split.shiftTrace, preparationSeedEvents,
    Word.PowerOfTwo.shiftTrace, scaleBodyEvents, negateEvents,
    ResourcePool.singleton, ResourcePool.ofList, ResourcePool.count, outside]

/-- Every coordinate outside native classical operations is absent from the
raw-recovery allowance. -/
lemma singleExposureEnvelope_count_nonclassical {width : Nat}
    (spec : ModulusSpec width) :
    ResourcePool.count event (singleExposureEnvelope model spec) = 0 := by
  simp only [singleExposureEnvelope, checkedExposureEnvelope, ResourcePool.count_add,
    preparation_count_zero event outside, checkedInverse_count_zero event outside]
  simp [selectedExposureEvents, exposureCopyEvents,
    NormalizedRecovery.Native.recoveryEvents,
    ResourcePool.ofList, ResourcePool.count, outside]

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
