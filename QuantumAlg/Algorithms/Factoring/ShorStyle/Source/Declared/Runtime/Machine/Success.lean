/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Recovery
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability

/-!
# The original finite retry floor for the genuine declared Shor machine

The actual packed output law transfers the original independent source bound.
Semiprime factors occur solely in the theorem-side postcondition and proof.
Actual execution needs only the original modulus input and rational failure
budget; the caller supplies no sample distribution, factor or prepared state.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

/-- Actual chronological completed retries attain the original factoring success threshold. -/
lemma output_success_probability_ge (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    FailureBudget.successThreshold budget ≤
      ((run base noQuantum N (Probability.Input.ofSemiprimeModel model)
        (retryCount N budget)).outputDistribution
          (environment (Probability.Input.ofSemiprimeModel model)) original).toOuterMeasure
          {value | Probability.ReturnedDeclaredFactor model value} := by
  let source := Probability.Input.ofSemiprimeModel model
  let sampling := PMF.independentReplicateVector (sourceOutcomePMF source) (retryCount N budget)
  let result := fun samples : List.Vector (SourceOutcome N) (retryCount N budget) =>
    NativeFactorScan.sourceResults source samples.toList
  let accepted : Set (CShape.Value (.option (.unsignedWord (modulusBits N)))) :=
    {value | Probability.ReturnedDeclaredFactor model value}
  have actual : ((run base noQuantum N source (retryCount N budget)).outputDistribution
      (environment source) original).toOuterMeasure accepted = sampling.toOuterMeasure (result
        ⁻¹' accepted) :=
    (congrArg (fun distribution : PMF (CShape.Value (.option (.unsignedWord (modulusBits N)))) =>
      distribution.toOuterMeasure accepted)
      (outputDistribution_eq base noQuantum N source (retryCount N budget) original)).trans
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

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
