/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled
import all QuantumAlg.Util.PMF.PairCount

/-!
# The original success floor for larger finite batches

Every source draw and ordered-key convention is unchanged. Additional terminal
draws preserve every feasible pair in an existing sixteen-draw subtranscript.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess

noncomputable section

private lemma batchValue_some_of_earlyFactor_atCount {N factor sampleCount : Nat}
    (sample : Fin (2 ^ residueSamplingBits N))
    (enough : 2 ≤ sampleCount)
    (earlyFactor : (preparedResidue sample).earlyFactor = some factor)
    (measurements : List.Vector (TerminalZMeasure.Outcome (measurementBits N)) sampleCount) :
    ∃ recovered, BatchRecovery.batchValue N (registerParameters N).m
      (registerParameters N).ell (measurements.map (preparedSampleOfMeasurement sample)) =
        some recovered := by
  have pairNonempty : measurements.toList.unorderedPairs ≠ [] := by
    intro empty
    have lengthEq := List.length_unorderedPairs measurements.toList
    rw [empty] at lengthEq
    simp only [List.length_nil, List.Vector.toList_length] at lengthEq
    have positive : 0 < Nat.choose sampleCount 2 := Nat.choose_pos enough
    omega
  rcases List.exists_cons_of_ne_nil pairNonempty with ⟨pair, remaining, pairEq⟩
  apply BatchRecovery.batchValue_eq_some_of_exists
  refine ⟨factor, ?_⟩
  rw [BatchRecovery.batchPairValues_eq_list, List.Vector.toList_map,
    List.unorderedPairs_map, List.map_map]
  apply List.mem_map.mpr
  refine ⟨pair, ?_, ?_⟩
  · rw [pairEq]
    exact List.mem_cons_self
  · change BatchRecovery.recoverPreparedPair N (registerParameters N).m
      (registerParameters N).ell
      (⟨preparedResidue sample, terminalBitsOfOutcome pair.1⟩,
        ⟨preparedResidue sample, terminalBitsOfOutcome pair.2⟩) = some factor
    rw [BatchRecovery.recoverPreparedPair_same_prepared, earlyFactor, Option.orElse_some]

/-- Every actual fixed-source branch with an early factor succeeds with probability one. -/
lemma fixed_eq_one_of_earlyFactor_atCount {N sampleCount : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (enough : 2 ≤ sampleCount)
    (earlyFactor : (preparedResidue sample).earlyFactor.isSome) :
    (fixedBatchOutputPMFAtCount model.input sample sampleCount).toOuterMeasure (accepts model) =
      1 := by
  cases earlyEq : (preparedResidue sample).earlyFactor with
  | none => simp only [earlyEq, Option.isSome_none, Bool.false_eq_true] at earlyFactor
  | some factor =>
      rw [fixedBatchOutputPMFAtCount, PMF.toOuterMeasure_map_apply,
        PMF.toOuterMeasure_apply_eq_one_iff]
      intro inputs supported
      have measurements : fixedBatchInputPMFAtCount model.input sample sampleCount =
          (PMF.independentReplicateVector
            (selectedOutcomePMF (parameterValue model.input sample)) sampleCount).map
              (fun values => values.map (preparedSampleOfMeasurement sample)) := by
        unfold fixedBatchInputPMFAtCount fixedPreparedSamplePMF
        exact (PMF.independentReplicateVector_map _ _ sampleCount).symm
      rw [measurements, PMF.mem_support_map_iff] at supported
      rcases supported with ⟨measurements, _measurementSupport, rfl⟩
      rcases batchValue_some_of_earlyFactor_atCount sample enough earlyEq measurements with
        ⟨recovered, result⟩
      exact ⟨recovered, result, batchValue_some_declared model result⟩


/-- The feasible-pair probability floor persists after any additional draws. -/
lemma fixed_hasPair_ge_of_count_ge {N sampleCount : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N)) (countLe : 16 ≤ sampleCount)
    (orderSufficient : ShortDLP.oracleFiberSpan (registerParameters N)
      (RSA.shortLogSecret model.pair.p model.pair.q) ≤ orderOf (preparedResidue sample).unit) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
      (fixedBatchInputPMFAtCount model.input sample sampleCount).toOuterMeasure
        {inputs | PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N
          (RSA.shortLogSecret model.pair.p model.pair.q) sample) inputs.toList} := by
  have original := fixed_hasPair_ge model sample orderSufficient
  change ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
    (fixedBatchInputPMFAtCount model.input sample 16).toOuterMeasure
      {inputs | PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N
        (RSA.shortLogSecret model.pair.p model.pair.q) sample) inputs.toList} at original
  have transport :
      (fixedBatchInputPMFAtCount model.input sample 16).toOuterMeasure
          {inputs | PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N
            (RSA.shortLogSecret model.pair.p model.pair.q) sample) inputs.toList} =
        (PMF.independentReplicate (fixedPreparedSamplePMF model.input sample) 16).toOuterMeasure
          {samples | PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N
            (RSA.shortLogSecret model.pair.p model.pair.q) sample) samples} := by
    unfold fixedBatchInputPMFAtCount
    rw [← PMF.independentReplicateVector_toList (fixedPreparedSamplePMF model.input sample) 16,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [transport] at original
  have more := PMF.independentReplicate_hasPairProbability_mono
    (fixedPreparedSamplePMF model.input sample)
    (FixedPreparedFeasibleNarrowGoodPair N
      (RSA.shortLogSecret model.pair.p model.pair.q) sample) countLe
  have bound := original.trans more
  dsimp only at bound
  rw [← PMF.independentReplicateVector_toList
    (fixedPreparedSamplePMF model.input sample) sampleCount,
    PMF.toOuterMeasure_map_apply] at bound
  exact bound

/-- Full all-pairs recovery inherits the larger transcript's feasible-pair floor. -/
lemma fixed_ge_of_order_of_count_ge {N sampleCount : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N)) (countLe : 16 ≤ sampleCount)
    (orderSufficient : ShortDLP.oracleFiberSpan (registerParameters N)
      (RSA.shortLogSecret model.pair.p model.pair.q) ≤ orderOf (preparedResidue sample).unit) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
      (fixedBatchOutputPMFAtCount model.input sample sampleCount).toOuterMeasure (accepts model)
        := by
  rw [fixedBatchOutputPMFAtCount, PMF.toOuterMeasure_map_apply]
  refine (fixed_hasPair_ge_of_count_ge model sample countLe orderSufficient).trans ?_
  apply PMF.toOuterMeasure_mono
  intro inputs feasible
  exact batchValue_accepts_of_feasiblePair model sample orderSufficient inputs feasible.1

/-- Every nonexceptional original sampler branch has the declared fixed-batch success floor. -/
lemma fixed_ge_of_samplerGood_of_count_ge {N sampleCount : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (countLe : 16 ≤ sampleCount)
    (samplerGood : ¬ RSA.FixedWidthSampling.SamplerExceptional model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount sample) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
      (fixedBatchOutputPMFAtCount model.input sample sampleCount).toOuterMeasure (accepts model)
        := by
  rcases model with ⟨bitWidth, pair, rfl, effective, keyGood⟩
  let model : GoodKeyModel pair.modulus := ⟨bitWidth, pair, rfl, effective, keyGood⟩
  cases earlyEq : (preparedResidue sample).earlyFactor with
  | some factor =>
      have earlyFactor : (preparedResidue sample).earlyFactor.isSome := by rw [earlyEq]; rfl
      exact sixteenSampleBatchFloor_le_one.trans_eq
        (fixed_eq_one_of_earlyFactor_atCount model sample (by omega) earlyFactor).symm
  | none =>
      have orderSufficient : RSA.GeneratorOrder.OrderSufficient bitWidth
          (RSA.shortLogSecret pair.p pair.q) (orderOf (preparedResidue sample).unit) := by
        by_contra insufficient
        apply samplerGood
        exact RSA.FixedWidthSampling.preparedOrderFailure_implies_samplerExceptional
          pair effective keyGood sample
          (by simpa only [preparedResidue, modulusBits, residueProposalCount] using earlyEq)
          (by simpa only [preparedResidue, modulusBits, residueProposalCount] using insufficient)
      exact fixed_ge_of_order_of_count_ge model sample countLe
        (model.orderSufficient_runtimeFiberSpan _ _ orderSufficient)


/-- The original same-source sampled batch returns a declared factor with the original floor. -/
lemma sampled_ge_of_count_ge {N sampleCount : Nat} (model : GoodKeyModel N)
    (countLe : 16 ≤ sampleCount) :
    successFloor model.bitWidth ≤
      (sampledBatchOutputPMFAtCount model.input sampleCount).toOuterMeasure (accepts model) := by
  have conditional := PMF.bind_eventProbability_ge_goodMass_mul
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N)))
    (fun sample => fixedBatchOutputPMFAtCount model.input sample sampleCount)
    (fun sample => RSA.FixedWidthSampling.SamplerExceptional model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount sample)
    (fun output => output ∈ accepts model)
    (ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ))
    (fun sample samplerGood => fixed_ge_of_samplerGood_of_count_ge model sample countLe samplerGood)
  exact (mul_le_mul_left (samplerGoodMass_ge model) _).trans conditional

/-- The original sampled batch's empty-result mass is bounded by the complementary floor. -/
lemma sampled_none_le_of_count_ge {N sampleCount : Nat} (model : GoodKeyModel N)
    (countLe : 16 ≤ sampleCount) :
    sampledBatchOutputPMFAtCount model.input sampleCount none ≤ 1 - successFloor model.bitWidth
      := by
  have complement :
      (sampledBatchOutputPMFAtCount model.input sampleCount).toOuterMeasure {output | output ∉
        accepts
        model} =
        1 - (sampledBatchOutputPMFAtCount model.input sampleCount).toOuterMeasure (accepts
          model) := by
    rw [PMF.eventProbability_eq_one_sub_complement
      (sampledBatchOutputPMFAtCount model.input sampleCount) (fun output => output ∉ accepts model)]
    simp only [not_not, Set.ofPred_mem_eq]
  have emptyFailure : ({none} : Set (Option Nat)) ⊆ {output | output ∉ accepts model} := by
    intro output member
    rw [Set.mem_singleton_iff] at member
    subst output
    exact not_accepts_none model
  calc
    sampledBatchOutputPMFAtCount model.input sampleCount none =
        (sampledBatchOutputPMFAtCount model.input sampleCount).toOuterMeasure {none} :=
      (PMF.toOuterMeasure_apply_singleton _ none).symm
    _ ≤ (sampledBatchOutputPMFAtCount model.input sampleCount).toOuterMeasure
        {output | output ∉ accepts model} :=
      PMF.toOuterMeasure_mono _ (fun _ member => emptyFailure member.1)
    _ = 1 - (sampledBatchOutputPMFAtCount model.input sampleCount).toOuterMeasure (accepts model) :=
      complement
    _ ≤ 1 - successFloor model.bitWidth := tsub_le_tsub_left (sampled_ge_of_count_ge model
      countLe) 1

-- Keep concrete twenty-member PMFs sealed during proof-only input conversion.
attribute [local irreducible] fixedBatchOutputPMFAtCount

/-- The exact twenty-member source floor, before charging sampler failure. -/
def twentySuccessFloor (bitWidth : Nat) : ENNReal :=
  (1 - ENNReal.ofReal (RSA.FixedWidthSampling.samplerFailureBound bitWidth)) *
    ENNReal.ofReal (BinomialTail.twentySampleBatchFloor : ℝ)

/-- The stronger rounded tradeoff relation gives the exact twenty-member Born floor. -/
lemma fixed_twenty_ge_of_order {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (tradeoff : (registerParameters N).m + 1 ≤ 2 * (registerParameters N).ell)
    (orderSufficient : ShortDLP.oracleFiberSpan (registerParameters N)
      (RSA.shortLogSecret model.pair.p model.pair.q) ≤ orderOf (preparedResidue sample).unit) :
    ENNReal.ofReal (BinomialTail.twentySampleBatchFloor : ℝ) ≤
      (fixedBatchOutputPMFAtCount model.input sample 20).toOuterMeasure (accepts model) := by
  have target : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ RSA.shortLogSecret model.pair.p model.pair.q := by
    rcases model with ⟨bitWidth, pair, rfl, effective, keyGood⟩
    exact RSA.targetUnit_eq_shortLog pair.p_prime pair.q_prime pair.p_ne_q
      pair.p_odd pair.q_odd (preparedResidue sample).unit
  have born := fixedPreparedSample_twenty_hasFeasibleNarrowGoodPair_ge model.input sample
    (RSA.shortLogSecret model.pair.p model.pair.q) model.shortLog_atLeastThree
    tradeoff model.shortLogSecret_pos model.shortLogSecret_lt target orderSufficient
  rw [← PMF.independentReplicateVector_toList (fixedPreparedSamplePMF model.input sample) 20,
    PMF.toOuterMeasure_map_apply] at born
  rw [fixedBatchOutputPMFAtCount, PMF.toOuterMeasure_map_apply]
  refine born.trans ?_
  apply PMF.toOuterMeasure_mono
  intro inputs feasible
  exact batchValue_accepts_of_feasiblePair model sample orderSufficient inputs feasible.1

/-- Every original nonexceptional source has the tighter twenty-member floor. -/
lemma fixed_twenty_ge_of_samplerGood {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (tradeoff : (registerParameters N).m + 1 ≤ 2 * (registerParameters N).ell)
    (samplerGood : ¬ RSA.FixedWidthSampling.SamplerExceptional model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount sample) :
    ENNReal.ofReal (BinomialTail.twentySampleBatchFloor : ℝ) ≤
      (fixedBatchOutputPMFAtCount model.input sample 20).toOuterMeasure (accepts model) := by
  rcases model with ⟨bitWidth, pair, rfl, effective, keyGood⟩
  let model : GoodKeyModel pair.modulus := ⟨bitWidth, pair, rfl, effective, keyGood⟩
  cases earlyEq : (preparedResidue sample).earlyFactor with
  | some factor =>
      have earlyFactor : (preparedResidue sample).earlyFactor.isSome := by rw [earlyEq]; rfl
      have floorLe : ENNReal.ofReal (BinomialTail.twentySampleBatchFloor : ℝ) ≤ 1 := by
        apply ENNReal.ofReal_le_one.mpr
        norm_num [BinomialTail.twentySampleBatchFloor,
          BinomialTail.atLeastTwoOfTwentyAtOneEighth]
      exact floorLe.trans_eq
        (fixed_eq_one_of_earlyFactor_atCount model sample (by norm_num) earlyFactor).symm
  | none =>
      have orderSufficient : RSA.GeneratorOrder.OrderSufficient bitWidth
          (RSA.shortLogSecret pair.p pair.q) (orderOf (preparedResidue sample).unit) := by
        by_contra insufficient
        apply samplerGood
        exact RSA.FixedWidthSampling.preparedOrderFailure_implies_samplerExceptional
          pair effective keyGood sample
          (by simpa only [preparedResidue, modulusBits, residueProposalCount] using earlyEq)
          (by simpa only [preparedResidue, modulusBits, residueProposalCount] using insufficient)
      exact fixed_twenty_ge_of_order model sample tradeoff
        (model.orderSufficient_runtimeFiberSpan _ _ orderSufficient)

/-- Bind the original source sampler to the twenty complete terminal/recovery executions. -/
lemma sampled_twenty_ge {N : Nat} (model : GoodKeyModel N)
    (tradeoff : (registerParameters N).m + 1 ≤ 2 * (registerParameters N).ell) :
    twentySuccessFloor model.bitWidth ≤
      (sampledBatchOutputPMFAtCount model.input 20).toOuterMeasure (accepts model) := by
  have conditional := PMF.bind_eventProbability_ge_goodMass_mul
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N)))
    (fun sample => fixedBatchOutputPMFAtCount model.input sample 20)
    (fun sample => RSA.FixedWidthSampling.SamplerExceptional model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount sample)
    (fun output => output ∈ accepts model)
    (ENNReal.ofReal (BinomialTail.twentySampleBatchFloor : ℝ))
    (fun sample samplerGood => fixed_twenty_ge_of_samplerGood model sample tradeoff samplerGood)
  exact (mul_le_mul_left (samplerGoodMass_ge model) _).trans conditional

/-- The tighter empty-output bound uses the same actual twenty-member recovery law. -/
lemma sampled_twenty_none_le {N : Nat} (model : GoodKeyModel N)
    (tradeoff : (registerParameters N).m + 1 ≤ 2 * (registerParameters N).ell) :
    sampledBatchOutputPMFAtCount model.input 20 none ≤ 1 - twentySuccessFloor model.bitWidth := by
  have complement :
      (sampledBatchOutputPMFAtCount model.input 20).toOuterMeasure {output | output ∉ accepts
        model} =
        1 - (sampledBatchOutputPMFAtCount model.input 20).toOuterMeasure (accepts model) := by
    rw [PMF.eventProbability_eq_one_sub_complement
      (sampledBatchOutputPMFAtCount model.input 20) (fun output => output ∉ accepts model)]
    simp only [not_not, Set.ofPred_mem_eq]
  calc
    sampledBatchOutputPMFAtCount model.input 20 none =
        (sampledBatchOutputPMFAtCount model.input 20).toOuterMeasure {none} :=
      (PMF.toOuterMeasure_apply_singleton _ none).symm
    _ ≤ (sampledBatchOutputPMFAtCount model.input 20).toOuterMeasure
        {output | output ∉ accepts model} := by
      apply PMF.toOuterMeasure_mono
      intro output member
      have equal : output = none := member.1
      subst output
      exact not_accepts_none model
    _ = 1 - (sampledBatchOutputPMFAtCount model.input 20).toOuterMeasure (accepts model) :=
      complement
    _ ≤ 1 - twentySuccessFloor model.bitWidth :=
      tsub_le_tsub_left (sampled_twenty_ge model tradeoff) 1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess
