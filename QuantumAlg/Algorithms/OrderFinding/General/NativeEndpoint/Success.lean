/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Distribution.Source
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.SourceEvent
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Analysis
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.SourceMass

/-!
# Recoverable native source outcomes succeed in the complete execution

Every phase outcome certified by the original orbit event maps through the
actual finite recovery tail to the true order. The native Born law identifies
the recoverable source mass with the independently analyzed source law.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The actual result inherits any proven bound on recoverable native Born outcomes. -/
theorem output_successProbability_ge_of_source {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model access).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState)
    (hregister : N ^ 2 ≤ 2 ^ t)
    {lower : ENNReal}
    (sourceBound : lower ≤
      (OrderFinding.Native.sourceOutcomePMF access).toOuterMeasure
        {outcome | NativeRecoverableOutcome
          (ZMod.unitOfCoprime x hinput.coprime) r outcome}) :
    lower ≤ ((run hinput access).outputDistribution input).toOuterMeasure
      {output | output = .optionSome (.unsignedWord
        (ClassicalAlgorithms.OrderRecovery.candidateWord t r))} := by
  let source := OrderFinding.Native.sourceOutcomePMF access
  let recovered : TerminalZMeasure.Outcome t → CShape.Value (outputShape t) :=
    fun outcome => recoveredValue hinput access (.bits outcome)
  let accepted : Set (CShape.Value (outputShape t)) :=
    {output | output = .optionSome (.unsignedWord
      (ClassicalAlgorithms.OrderRecovery.candidateWord t r))}
  have actual : (run hinput access).outputDistribution input =
      source.map recovered := outputDistribution_eq hinput access input valid
  refine sourceBound.trans ?_
  calc
    source.toOuterMeasure
        {outcome | NativeRecoverableOutcome
          (ZMod.unitOfCoprime x hinput.coprime) r outcome} ≤
        source.toOuterMeasure (recovered ⁻¹' accepted) := by
      apply PMF.toOuterMeasure_mono
      intro outcome recoverable
      change ClassicalRoutines.OrderRecovery.Native.encodeOutput
          (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
            (recoverySpec hinput access) (semanticInput hinput access outcome)) =
        .optionSome (.unsignedWord
          (ClassicalAlgorithms.OrderRecovery.candidateWord t r))
      rw [recoverUnitOrder_eq_some_of_recoverableOutcome hinput access
        (order_fits_candidateWord hinput hregister) recoverable.1]
      rfl
    _ = (source.map recovered).toOuterMeasure accepted :=
      (PMF.toOuterMeasure_map_apply recovered source accepted).symm
    _ = ((run hinput access).outputDistribution input).toOuterMeasure accepted :=
      (congrArg (fun distribution : PMF (CShape.Value (outputShape t)) =>
        distribution.toOuterMeasure accepted) actual).symm

/-- The complete native order-finding result has the original public-window
success lower bound, including the finite small-modulus cases. -/
theorem output_successProbability_ge {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model access).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    ENNReal.ofReal (orderFindingOutputSuccessLowerBound r) ≤
      ((run hinput access).outputDistribution input).toOuterMeasure
        {output | output = .optionSome (.unsignedWord
          (ClassicalAlgorithms.OrderRecovery.candidateWord t r))} := by
  apply output_successProbability_ge_of_source hinput access input valid hregister
  calc
    ENNReal.ofReal (orderFindingOutputSuccessLowerBound r) ≤
        ENNReal.ofReal (orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime x hinput.coprime)
          (orderFindingPublicOutcomeProbability t r)) :=
      ENNReal.ofReal_le_ofReal
        (SourceAnalysis.sourceOutputSuccessLowerBound hinput hregister hupper)
    _ = (OrderFinding.Native.sourceOutcomePMF access).toOuterMeasure
        {outcome | NativeRecoverableOutcome
          (ZMod.unitOfCoprime x hinput.coprime) r outcome} :=
      (nativeRecoverableMass_eq_sourceSuccessMass hinput access).symm

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
