/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Probability.Members
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Batch
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Batch.Values
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Original complete recovery law of the measured parent kernels

Every terminal is the paid original parent write of a real measured member.
The actual parent recovery kernel retains the same source draw and complete
all-pairs value. Only original finite source-distribution identities are used
[EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program.Probability

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- The unchanged original finite optional-factor shape. -/
abbrev Factor (N : Nat) := (LatticeBatchRecoveryOutput.OutputShape N).Value

/-- Original sampled-batch distribution at the public member configuration. -/
def batchDistribution {N : Nat} (input : Input N) : PMF (Factor N) :=
  (sampledBatchOutputPMFAtCount input membersPerBatch).map LatticeBatchRecoveryOutput.outputValue

/-- The source's complete all-pairs recovery value on one draw and its terminals. -/
def recoveredValue {N : Nat} (_input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (values : List.Vector (Terminal N) membersPerBatch) : Factor N :=
  LatticeBatchRecoveryOutput.outputValue
    (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N)
      (values.map (preparedSampleOfMeasurement sample)))

private lemma rsaMeasuredProbability_batchDistribution_bind {N : Nat} (input : Input N) :
    batchDistribution input =
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind fun sample =>
        (PMF.independentReplicateVector
          (selectedOutcomePMF (parameterValue input sample)) membersPerBatch).map
            (recoveredValue input sample) := by
  unfold batchDistribution sampledBatchOutputPMFAtCount
  rw [PMF.map_bind]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))))
  funext sample
  unfold fixedBatchOutputPMFAtCount fixedBatchInputPMFAtCount fixedPreparedSamplePMF
  rw [← PMF.independentReplicateVector_map, PMF.map_comp, PMF.map_comp]
  rfl

/-- Exact finite moment of the same source draw and complete conditional recovery. -/
lemma rsaMeasuredProbability_batchDistribution_weighted {N : Nat} (input : Input N)
    (weight : Factor N → ℂ) :
    (∑ factor : Factor N, ((batchDistribution input factor).toReal : ℂ) * weight factor) =
      ∑ sample : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          ∑ values : List.Vector (Terminal N) membersPerBatch,
            ((PMF.independentReplicateVector
              (selectedOutcomePMF (parameterValue input sample)) membersPerBatch values).toReal
                : ℂ) * weight (recoveredValue input sample values) := by
  rw [rsaMeasuredProbability_batchDistribution_bind, PMF.sum_bind_toReal_mul]
  apply Finset.sum_congr rfl
  intro sample _
  rw [PMF.sum_map_toReal_mul, PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  rfl

variable (base : RuntimeCtx .quantum) (N count : Nat)

/-- The chronological original parent factor cells read by the actual final selector. -/
def factorRead (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    Fin count → Factor N :=
  fun batch => stored.read (FirstAccepted.cellRead
    (Recycling.ClassicalFrame.factorRef base N count batch))

private lemma rsaMeasuredProbability_memberStores_factor (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin membersPerBatch) (values : List.Vector (Terminal N) length)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    factorRead base N count
        (memberStores base N count batch length indices values stored) =
      factorRead base N count stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      refine (ih (fun index => indices index.succ) values.tail _).trans ?_
      funext previous
      exact Store.read_write_other stored
        (Recycling.ClassicalFrame.packedRef base N count batch (indices 0))
        (Recycling.ClassicalFrame.factorRef base N count previous).toCStorageRef _
        (Recycling.ClassicalFrame.rsaRecyclingFrame_packed_factor_separate
          base N count batch previous (indices 0))

private lemma rsaMeasuredProbability_memberStores_sample (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin membersPerBatch) (values : List.Vector (Terminal N) length)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    sourceStoredSample
        (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch))
        (memberStores base N count batch length indices values stored) =
      sourceStoredSample
        (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch))
        stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      refine (ih (fun index => indices index.succ) values.tail _).trans ?_
      exact congrArg (BitWord.Random.sampleEquiv (residueSamplingBits N))
        (Store.read_write_other stored
          (Recycling.ClassicalFrame.packedRef base N count batch (indices 0))
          (Recycling.ClassicalFrame.sampleRef base N count batch).toCStorageRef _
          (Recycling.ClassicalFrame.rsaRecyclingFrame_packed_sample_separate
            base N count batch batch (indices 0)))

private lemma rsaMeasuredProbability_actual_preparedSamples
    (sample : Fin (2 ^ residueSamplingBits N)) (batch : Fin count)
    (values : List.Vector (Terminal N) membersPerBatch)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    LatticePairRecoveryBatch.preparedSamples (preparedResidue sample)
        (parentTerminals base N count batch)
        (memberStores base N count batch membersPerBatch id values stored) =
      values.map (preparedSampleOfMeasurement sample) := by
  apply List.Vector.ext
  intro index
  simp only [LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map,
    List.Vector.get_ofFn]
  refine Eq.trans ?_ (List.Vector.get_map values (preparedSampleOfMeasurement sample) index).symm
  apply congrArg (fun bits : Terminal N =>
    ({ prepared := preparedResidue sample, terminalBits := bits } : PreparedBatchSample N))
  funext bit
  have actual := rsaMeasuredProbability_memberStores_read base N count batch membersPerBatch id
    Function.injective_id values stored index
  unfold BatchMachine.sourceBits
  change ((memberStores base N count batch membersPerBatch id values stored).read
    (.bitsGet (parentTerminals base N count batch index) bit)).toBool = _
  change ((packedRead base N count batch index
    (memberStores base N count batch membersPerBatch id values stored)).bitGet bit).toBool = _
  exact congrArg (fun value : CShape.Value (.bits (measurementBits N)) =>
    (value.bitGet bit).toBool) actual

/-- The exact actual recovery parent write updates only its own original factor coordinate. -/
lemma rsaMeasuredProbability_recovery_after_members (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (batch : Fin count)
    (values : List.Vector (Terminal N) membersPerBatch)
    (stored : Store (Recycling.ClassicalFrame.context base N count))
    (sampleStored : sourceStoredSample
      (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch)) stored =
        sample) :
    factorRead base N count
        (recoveryParentStore base N count batch
          (memberStores base N count batch membersPerBatch id values stored)) =
      Function.update (factorRead base N count stored) batch
        (recoveredValue input sample values) := by
  have sampleAfter := (rsaMeasuredProbability_memberStores_sample base N count batch
    membersPerBatch id values stored).trans sampleStored
  funext previous
  by_cases same : previous = batch
  · subst previous
    rw [Function.update_self]
    refine (Store.read_write_same _ (Recycling.ClassicalFrame.factorRef base N count batch)
      _).trans ?_
    unfold LatticeFixedBatchRecoveryMachine.batchValue
    rw [sampleAfter]
    exact congrArg (fun samples : List.Vector (PreparedBatchSample N) membersPerBatch =>
      LatticeBatchRecoveryOutput.outputValue
        (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N) samples))
      (rsaMeasuredProbability_actual_preparedSamples base N count sample batch values stored)
  · rw [Function.update_of_ne same]
    refine (Store.read_write_other _ (Recycling.ClassicalFrame.factorRef base N count batch)
      (Recycling.ClassicalFrame.factorRef base N count previous).toCStorageRef _ ?_).trans
      (congrArg (fun observed : Fin count → Factor N => observed previous)
        (rsaMeasuredProbability_memberStores_factor base N count batch membersPerBatch id
          values stored))
    intro equalKeys
    exact same ((Recycling.ClassicalFrame.rsaRecyclingFrame_factorRef_distinct N base count
      equalKeys).symm)

/-- Conditional on its actual source, the real batch kernel has the original recovery moment. -/
lemma rsaMeasuredProbability_batchBody_factorKernel (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (batch : Fin count)
    (weight : (Fin count → Factor N) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count))
    (parameter : parameterRead base N count batch stored = parameterValue input sample)
    (sampleStored : sourceStoredSample
      (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch)) stored =
        sample) :
    batchBodyParentReferenceKernel base N count batch
        (fun after => weight (factorRead base N count after)) stored =
      ∑ values : List.Vector (Terminal N) membersPerBatch,
        ((PMF.independentReplicateVector
          (selectedOutcomePMF (parameterValue input sample)) membersPerBatch values).toReal : ℂ) *
            weight (Function.update (factorRead base N count stored) batch
              (recoveredValue input sample values)) := by
  have actual := rsaMeasuredProbability_membersKernel_iid base N count batch
    (fun after => weight (factorRead base N count (recoveryParentStore base N count batch after)))
    stored
  unfold batchBodyParentReferenceKernel
  refine actual.trans ?_
  rw [parameter]
  apply Finset.sum_congr rfl
  intro values _
  exact congrArg (fun factors : Fin count → Factor N =>
    ((PMF.independentReplicateVector
      (selectedOutcomePMF (parameterValue input sample)) membersPerBatch values).toReal : ℂ) *
        weight factors)
    (rsaMeasuredProbability_recovery_after_members base N count input sample batch values stored
      sampleStored)

/-- Every fresh native source leaves the existing factor destinations unchanged. -/
lemma rsaMeasuredProbability_sourceStore_factors (input : Input N) (batch : Fin count)
    (stored : Store (Recycling.ClassicalFrame.context base N count))
    (sample : Fin (2 ^ residueSamplingBits N)) :
    factorRead base N count
        (sourceStore N (Recycling.ClassicalFrame.sampleRef base N count batch)
          (Recycling.ClassicalFrame.parameterRef base N count batch) stored sample) =
      factorRead base N count stored := by
  rw [rsaMeasuredParent_sourceStore_value N _ _ input]
  funext previous
  exact (Store.read_write_other _ _ _ _
    (Recycling.ClassicalFrame.rsaRecyclingFrame_parameter_factor_separate
      base N count batch previous)).trans
    (Store.read_write_other _ _ _ _
      (Recycling.ClassicalFrame.rsaRecyclingFrame_sample_factor_separate
        base N count batch previous))

/-- The same actual retained draw decodes to the original finite source label. -/
lemma rsaMeasuredProbability_sourceStore_sample (input : Input N) (batch : Fin count)
    (stored : Store (Recycling.ClassicalFrame.context base N count))
    (sample : Fin (2 ^ residueSamplingBits N)) :
    sourceStoredSample
        (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch))
        (sourceStore N (Recycling.ClassicalFrame.sampleRef base N count batch)
          (Recycling.ClassicalFrame.parameterRef base N count batch) stored sample) = sample := by
  unfold sourceStoredSample
  rw [rsaMeasuredParent_sourceStore_sample N _ _ input stored sample
    (Ne.symm (Recycling.ClassicalFrame.rsaRecyclingFrame_sample_parameter_separate
      base N count batch batch)), ← ShorStyle.Canonical.Sampler.PackedSample.decoded_sample]
  exact Equiv.apply_symm_apply _ _

/-- A fresh actual complete batch has the original factor PMF and keeps all other factors. -/
lemma rsaMeasuredProbability_nextBatch_factorKernel (input : Input N) (batch : Fin count)
    (weight : (Fin count → Factor N) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    nextBatchParentReferenceKernel base N count batch
        (fun after => weight (factorRead base N count after)) stored =
      ∑ factor : Factor N, ((batchDistribution input factor).toReal : ℂ) *
        weight (Function.update (factorRead base N count stored) batch factor) := by
  rw [rsaMeasuredProbability_batchDistribution_weighted]
  unfold nextBatchParentReferenceKernel
  apply Finset.sum_congr rfl
  intro sample _
  apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  have actual := rsaMeasuredProbability_batchBody_factorKernel base N count input sample batch
    weight (sourceStore N (Recycling.ClassicalFrame.sampleRef base N count batch)
      (Recycling.ClassicalFrame.parameterRef base N count batch) stored sample)
    (rsaMeasuredParent_sourceStore_parameter N _ _ input stored sample)
    (rsaMeasuredProbability_sourceStore_sample base N count input batch stored sample)
  simpa only [rsaMeasuredProbability_sourceStore_factors base N count input] using actual

end

end QuantumAlg.Factoring.RSA.Measured.Program.Probability
