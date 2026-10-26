/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Fixed

/-!
# Original uniformly sampled batch success and empty-output ceiling

The actual raw source is the uniform fixed-width residue proposal integer.
Its exact exceptional-event mass and the original sampler bound supply the
good source mass. Binding the same fixed-source sixteen-measurement recovery
law gives the sampler-adjusted declared-factor floor without changing its
shared source or adding an execution wrapper.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess

noncomputable section

/-- The original uniform source has at least the complement of the stated sampler loss. -/
lemma samplerGoodMass_ge {N : Nat} (model : GoodKeyModel N) :
    1 - ENNReal.ofReal (RSA.FixedWidthSampling.samplerFailureBound model.bitWidth) ≤
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).toOuterMeasure
        {sample | ¬ RSA.FixedWidthSampling.SamplerExceptional model.pair
          (model.bitWidth / 64) (modulusBits N) residueProposalCount sample} := by
  let distribution := PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))
  let exceptional := fun sample : Fin (2 ^ residueSamplingBits N) =>
    RSA.FixedWidthSampling.SamplerExceptional model.pair (model.bitWidth / 64)
      (modulusBits N) residueProposalCount sample
  have fractionAtEq : RSA.FixedWidthSampling.samplerExceptionalFractionAt model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount =
      RSA.FixedWidthSampling.samplerExceptionalFraction model.pair := by
    rw [model.modulusBits_eq]
    rfl
  have goodMassEq : distribution.toOuterMeasure {sample | ¬ exceptional sample} =
      1 - ENNReal.ofReal (RSA.FixedWidthSampling.samplerExceptionalFractionAt model.pair
        (model.bitWidth / 64) (modulusBits N) residueProposalCount) := by
    rw [PMF.eventProbability_eq_one_sub_complement distribution
      (fun sample => ¬ exceptional sample)]
    simp only [not_not]
    congr 1
    exact RSA.FixedWidthSampling.uniformBits_samplerExceptionalMass_eq_at model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount
  have widthEffective : 512 ≤ model.bitWidth := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using model.effective
  have fractionLe : RSA.FixedWidthSampling.samplerExceptionalFractionAt model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount ≤
      RSA.FixedWidthSampling.samplerFailureBound model.bitWidth :=
    fractionAtEq.le.trans
      (RSA.FixedWidthSampling.samplerExceptionalFraction_lt_samplerFailureBound
        model.pair widthEffective).le
  change _ ≤ distribution.toOuterMeasure {sample | ¬ exceptional sample}
  rw [goodMassEq]
  exact tsub_le_tsub_left (ENNReal.ofReal_le_ofReal fractionLe) 1

/-- The original same-source sampled batch returns a declared factor with the original floor. -/
lemma sampled_ge {N : Nat} (model : GoodKeyModel N) :
    successFloor model.bitWidth ≤
      (sampledBatchOutputPMF model.input).toOuterMeasure (accepts model) := by
  have conditional := PMF.bind_eventProbability_ge_goodMass_mul
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N)))
    (fun sample => fixedBatchOutputPMF model.input sample)
    (fun sample => RSA.FixedWidthSampling.SamplerExceptional model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount sample)
    (fun output => output ∈ accepts model)
    (ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ))
    (fun sample samplerGood => fixed_ge_of_samplerGood model sample samplerGood)
  exact (mul_le_mul_left (samplerGoodMass_ge model) _).trans conditional

/-- The original sampled batch's empty-result mass is bounded by the complementary floor. -/
lemma sampled_none_le {N : Nat} (model : GoodKeyModel N) :
    sampledBatchOutputPMF model.input none ≤ 1 - successFloor model.bitWidth := by
  have complement :
      (sampledBatchOutputPMF model.input).toOuterMeasure {output | output ∉ accepts model} =
        1 - (sampledBatchOutputPMF model.input).toOuterMeasure (accepts model) := by
    rw [PMF.eventProbability_eq_one_sub_complement
      (sampledBatchOutputPMF model.input) (fun output => output ∉ accepts model)]
    simp only [not_not, Set.ofPred_mem_eq]
  have emptyFailure : ({none} : Set (Option Nat)) ⊆ {output | output ∉ accepts model} := by
    intro output member
    rw [Set.mem_singleton_iff] at member
    subst output
    exact not_accepts_none model
  calc
    sampledBatchOutputPMF model.input none =
        (sampledBatchOutputPMF model.input).toOuterMeasure {none} :=
      (PMF.toOuterMeasure_apply_singleton _ none).symm
    _ ≤ (sampledBatchOutputPMF model.input).toOuterMeasure
        {output | output ∉ accepts model} :=
      PMF.toOuterMeasure_mono _ (fun _ member => emptyFailure member.1)
    _ = 1 - (sampledBatchOutputPMF model.input).toOuterMeasure (accepts model) := complement
    _ ≤ 1 - successFloor model.bitWidth := tsub_le_tsub_left (sampled_ge model) 1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess
