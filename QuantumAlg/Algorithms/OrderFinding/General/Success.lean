/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Distribution
import all QuantumAlg.Algorithms.OrderFinding.General.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.General.Model

/-!
# Original general order-finding success for the actual native run

The original source probability lower bound applies to its recoverable Born
outcomes throughout the original register window. The actual recovery theorem
maps every such outcome to the true order. Arbitrary other samples retain the
source's optional-candidate behavior; they are not all declared successful.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The original recoverable source outcomes carry the original lower bound. -/
theorem source_recoverableProbability_ge {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (hregister : N ^ 2 ≤ 2 ^ t) (hupper : 2 ^ t < 2 * N ^ 2) :
    (successLB r).value ≤
      ((measurement t width).outcomePMF (BornBridge.evolvedState A)).toOuterMeasure
        {outcome | RecoverableOutcome (ZMod.unitOfCoprime x hinput.coprime) r outcome} := by
  calc
    ENNReal.ofReal (orderFindingOutputSuccessLowerBound r) ≤
        ENNReal.ofReal (orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime x hinput.coprime) (orderFindingPublicOutcomeProbability t r)) :=
      ENNReal.ofReal_le_ofReal (sourceOutputSuccessLowerBound hinput hregister hupper)
    _ = _ := (BornBridge.sourceMeasurementModel hinput A).symm

/-- The actual complete native result returns the true order with the original source bound. -/
theorem output_successProbability_ge {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState)
    (hregister : N ^ 2 ≤ 2 ^ t) (hupper : 2 ^ t < 2 * N ^ 2) :
    (successLB r).value ≤
      ((run hinput A).outputDistribution input).toOuterMeasure
        {output | SuccessfulOutcome r output} := by
  let source := (measurement t width).outcomePMF (BornBridge.evolvedState A)
  let recovered : Outcome t → CShape.Value (outputShape t) := fun outcome =>
    ClassicalRoutines.OrderRecovery.Native.encodeOutput
      (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
        (recoverySpec hinput A) (semanticInput hinput A outcome))
  let accepted : Set (CShape.Value (outputShape t)) := {output | SuccessfulOutcome r output}
  have actual : (run hinput A).outputDistribution input = source.map recovered :=
    outputDistribution_eq hinput A input valid
  refine (source_recoverableProbability_ge hinput A hregister hupper).trans ?_
  calc
    source.toOuterMeasure
        {outcome | RecoverableOutcome (ZMod.unitOfCoprime x hinput.coprime) r outcome} ≤
        source.toOuterMeasure (recovered ⁻¹' accepted) := by
      apply PMF.toOuterMeasure_mono
      intro outcome recoverable
      change ClassicalRoutines.OrderRecovery.Native.encodeOutput
          (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
            (recoverySpec hinput A) (semanticInput hinput A outcome)) =
        .optionSome (.unsignedWord
          (ClassicalAlgorithms.OrderRecovery.candidateWord t r))
      rw [recoverUnitOrder_eq_some_of_recoverableOutcome hinput A
        (order_fits_candidateWord hinput hregister) recoverable.1]
      rfl
    _ = (source.map recovered).toOuterMeasure accepted :=
      (PMF.toOuterMeasure_map_apply recovered source accepted).symm
    _ = ((run hinput A).outputDistribution input).toOuterMeasure accepted :=
      (congrArg (fun distribution : PMF (CShape.Value (outputShape t)) =>
        distribution.toOuterMeasure accepted) actual).symm

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
