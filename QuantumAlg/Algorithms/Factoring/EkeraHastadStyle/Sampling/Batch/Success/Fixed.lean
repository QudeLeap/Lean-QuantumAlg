/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Widths
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.PreparedAttempt.Born

/-!
# Original fixed-source batch success on nonexceptional sampler branches

All sixteen terminal draws share the same prepared residue. An early factor
already makes the complete pair scan succeed. Otherwise the original sampler
event supplies sufficient order, and the raw Born feasible-pair theorem feeds
the unchanged full recovery of all 120 pairs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess

noncomputable section

private theorem fixedBatchInputPMF_measurements {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    fixedBatchInputPMF input sample =
      (PMF.independentReplicateVector (selectedOutcomePMF (parameterValue input sample)) 16).map
        (fun measurements => measurements.map (preparedSampleOfMeasurement sample)) := by
  unfold fixedBatchInputPMF fixedPreparedSamplePMF
  exact (PMF.independentReplicateVector_map _ _ 16).symm

private theorem batchValue_some_of_earlyFactor {N factor : Nat}
    (sample : Fin (2 ^ residueSamplingBits N))
    (earlyFactor : (preparedResidue sample).earlyFactor = some factor)
    (measurements : List.Vector (TerminalZMeasure.Outcome (measurementBits N)) 16) :
    ∃ recovered, BatchRecovery.batchValue N (registerParameters N).m
      (registerParameters N).ell (measurements.map (preparedSampleOfMeasurement sample)) =
        some recovered := by
  have pairNonempty : measurements.toList.unorderedPairs ≠ [] := by
    intro empty
    have lengthEq := List.length_unorderedPairs measurements.toList
    rw [empty] at lengthEq
    simp only [List.length_nil, List.Vector.toList_length] at lengthEq
    norm_num [Nat.choose] at lengthEq
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
theorem fixed_eq_one_of_earlyFactor {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (earlyFactor : (preparedResidue sample).earlyFactor.isSome) :
    (fixedBatchOutputPMF model.input sample).toOuterMeasure (accepts model) = 1 := by
  cases earlyEq : (preparedResidue sample).earlyFactor with
  | none => simp only [earlyEq, Option.isSome_none, Bool.false_eq_true] at earlyFactor
  | some factor =>
      rw [fixedBatchOutputPMF, PMF.toOuterMeasure_map_apply,
        PMF.toOuterMeasure_apply_eq_one_iff]
      intro inputs supported
      rw [fixedBatchInputPMF_measurements, PMF.mem_support_map_iff] at supported
      rcases supported with ⟨measurements, _measurementSupport, rfl⟩
      rcases batchValue_some_of_earlyFactor sample earlyEq measurements with ⟨recovered, result⟩
      exact ⟨recovered, result, batchValue_some_declared model result⟩

private theorem targetPower {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ RSA.shortLogSecret model.pair.p model.pair.q := by
  rcases model with ⟨bitWidth, pair, rfl, effective, keyGood⟩
  exact RSA.targetUnit_eq_shortLog pair.p_prime pair.q_prime pair.p_ne_q
    pair.p_odd pair.q_odd (preparedResidue sample).unit

/-- The raw sixteen-vector law inherits the original raw list feasible-pair probability floor. -/
theorem fixed_hasPair_ge {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (orderSufficient : ShortDLP.oracleFiberSpan (registerParameters N)
      (RSA.shortLogSecret model.pair.p model.pair.q) ≤ orderOf (preparedResidue sample).unit) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
      (fixedBatchInputPMF model.input sample).toOuterMeasure
        {inputs | PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N
          (RSA.shortLogSecret model.pair.p model.pair.q) sample) inputs.toList} := by
  have born := fixedPreparedSample_sixteen_hasFeasibleNarrowGoodPair_ge model.input sample
    (RSA.shortLogSecret model.pair.p model.pair.q) model.shortLog_atLeastThree
    (GoodKeyModel.tradeoff_sufficient (N := N)) model.shortLogSecret_pos model.shortLogSecret_lt
    (targetPower model sample) orderSufficient
  rw [← PMF.independentReplicateVector_toList (fixedPreparedSamplePMF model.input sample) 16,
    PMF.toOuterMeasure_map_apply] at born
  exact born

/-- A feasible pair in the complete fixed batch yields a declared factor under the original key. -/
theorem batchValue_accepts_of_feasiblePair {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (orderSufficient : ShortDLP.oracleFiberSpan (registerParameters N)
      (RSA.shortLogSecret model.pair.p model.pair.q) ≤ orderOf (preparedResidue sample).unit)
    (inputs : List.Vector (PreparedBatchSample N) 16)
    (feasible : PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N
      (RSA.shortLogSecret model.pair.p model.pair.q) sample) inputs.toList) :
    BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell inputs ∈
      accepts model := by
  rcases model with ⟨bitWidth, pair, rfl, effective, keyGood⟩
  let model : GoodKeyModel pair.modulus := ⟨bitWidth, pair, rfl, effective, keyGood⟩
  rcases batchValue_eq_some_of_fixedPreparedFeasibleNarrowGoodPair sample
    pair.p_prime pair.q_prime pair.p_ne_q pair.p_odd pair.q_odd model.shortLog_atLeastThree
    model.shortLogSecret_pos model.shortLogSecret_lt orderSufficient inputs feasible with
      ⟨factor, result⟩
  exact ⟨factor, result, batchValue_some_declared model result⟩

/-- Sufficient order transfers the same-source Born floor to the original complete recovery law. -/
theorem fixed_ge_of_order {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (orderSufficient : ShortDLP.oracleFiberSpan (registerParameters N)
      (RSA.shortLogSecret model.pair.p model.pair.q) ≤ orderOf (preparedResidue sample).unit) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
      (fixedBatchOutputPMF model.input sample).toOuterMeasure (accepts model) := by
  rw [fixedBatchOutputPMF, PMF.toOuterMeasure_map_apply]
  refine (fixed_hasPair_ge model sample orderSufficient).trans ?_
  apply PMF.toOuterMeasure_mono
  intro inputs feasible
  exact batchValue_accepts_of_feasiblePair model sample orderSufficient inputs feasible.1

/-- Every nonexceptional original sampler branch has the declared fixed-batch success floor. -/
theorem fixed_ge_of_samplerGood {N : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (samplerGood : ¬ RSA.FixedWidthSampling.SamplerExceptional model.pair
      (model.bitWidth / 64) (modulusBits N) residueProposalCount sample) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤
      (fixedBatchOutputPMF model.input sample).toOuterMeasure (accepts model) := by
  rcases model with ⟨bitWidth, pair, rfl, effective, keyGood⟩
  let model : GoodKeyModel pair.modulus := ⟨bitWidth, pair, rfl, effective, keyGood⟩
  cases earlyEq : (preparedResidue sample).earlyFactor with
  | some factor =>
      have earlyFactor : (preparedResidue sample).earlyFactor.isSome := by rw [earlyEq]; rfl
      exact sixteenSampleBatchFloor_le_one.trans_eq
        (fixed_eq_one_of_earlyFactor model sample earlyFactor).symm
  | none =>
      have orderSufficient : RSA.GeneratorOrder.OrderSufficient bitWidth
          (RSA.shortLogSecret pair.p pair.q) (orderOf (preparedResidue sample).unit) := by
        by_contra insufficient
        apply samplerGood
        exact RSA.FixedWidthSampling.preparedOrderFailure_implies_samplerExceptional
          pair effective keyGood sample
          (by simpa only [preparedResidue, modulusBits, residueProposalCount] using earlyEq)
          (by simpa only [preparedResidue, modulusBits, residueProposalCount] using insufficient)
      exact fixed_ge_of_order model sample
        (model.orderSufficient_runtimeFiberSpan _ _ orderSufficient)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess
