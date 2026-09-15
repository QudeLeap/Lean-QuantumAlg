/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Recovery
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Original retry success for the complete actual native Shor output

The success probability is taken from the one real circuit's complete Output.
The actual output law and the preserved source recovery event transfer the
original independent retry bound. The input has no supplied sample law,
factor, seed state or relation between its classical frame and external Ref.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

noncomputable section

/-- Complete actual output reaches the original source threshold at the original retry count. -/
theorem output_success_probability_ge {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) {Reference : Register}
    (input : Execution.Input pre Reference) :
    FailureBudget.successThreshold budget ≤
      ((run (Probability.Input.ofSemiprimeModel model) (retryCount N budget)).outputDistribution
        input).toOuterMeasure {value | Probability.ReturnedDeclaredFactor model value} := by
  let source := Probability.Input.ofSemiprimeModel model
  let sampling := PMF.independentReplicateVector (sourceOutcomePMF source) (retryCount N budget)
  let result := fun samples : List.Vector (SourceOutcome N) (retryCount N budget) =>
    NativeFactorScan.sourceResults source samples.toList
  let accepted : Set (outputShape N).Value :=
    {value | Probability.ReturnedDeclaredFactor model value}
  have actual : ((run source (retryCount N budget)).outputDistribution input).toOuterMeasure
      accepted = sampling.toOuterMeasure (result ⁻¹' accepted) :=
    (congrArg (fun distribution : PMF (outputShape N).Value =>
      distribution.toOuterMeasure accepted)
      (outputDistribution_eq source (retryCount N budget) input)).trans
        (PMF.toOuterMeasure_map_apply result sampling accepted)
  have preserved : {samples | Probability.SuccessfulSamples model budget samples} ⊆
      result ⁻¹' accepted :=
    fun samples successful => NativeFactorScan.sourceResults_successfulSamples
      model budget samples successful
  calc
    FailureBudget.successThreshold budget ≤
        sampling.toOuterMeasure {samples | Probability.SuccessfulSamples model budget samples} :=
      Probability.repeatDistribution_successfulSamples_probability_ge model budget wellFormed
    _ ≤ sampling.toOuterMeasure (result ⁻¹' accepted) := MeasureTheory.measure_mono preserved
    _ = _ := actual.symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
