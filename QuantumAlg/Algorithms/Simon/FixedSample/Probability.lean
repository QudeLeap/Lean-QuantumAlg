/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Model
import all QuantumAlg.Util.PMF
import Mathlib.Data.Vector.Mem

/-!
# The original finite-sample Simon probability bound

The supplied circuit's original single-attempt Born law and source promise
bound each wrong nonzero candidate. The finite union bound applies to its
exact independent vector distribution at count `n + κ`, giving failure at
most `2⁻κ`. The separate actual execution theorem establishes this same joint
law through real finite measurement and reset; no runtime is defined here.
-/

namespace QuantumAlg.SimonsProblem.FixedSample

open Simon

noncomputable section

universe u

/-- Ordered semantic rows decoded from one exact measured batch. -/
def batchSamples {n count : Nat} (batch : List.Vector (Outcome n) count) :
    Samples count n :=
  fun index => decodeWord (batch.get index)

/-- The actual measured batch uniquely determines the represented nonzero
hidden mask. -/
def GoodBatch {n count : Nat} (secret : Word n)
    (batch : List.Vector (Outcome n) count) : Prop :=
  ClassicalAlgorithms.GF2.HasUniqueNonzeroSolution
    (batchSamples batch) secret

/-- The mathematical row-space rank is exactly the pivot count computed by
the polynomial reducer on the same observed batch. -/
lemma batchMatrixRank_eq_reducerPivotCount {n count : Nat}
    (batch : List.Vector (Outcome n) count) :
    (ClassicalAlgorithms.GF2.sampleMatrix
        (batchSamples batch)).rank =
      (ClassicalAlgorithms.GF2.reduce
        (batchSamples batch)).pivotCount := by
  exact
    ClassicalAlgorithms.GF2.sampleMatrix_rank_eq_reduce_pivotCount
      (batchSamples batch)

/-- A successful fixed batch satisfies the reducer's concrete rank condition:
row reduction exposes exactly one free column for back substitution. -/
lemma goodBatch_hasSoleFreeColumn {n count : Nat} {secret : Word n}
    {batch : List.Vector (Outcome n) count} (good : GoodBatch secret batch) :
    ∃ free,
      ClassicalAlgorithms.GF2.soleFreeColumn?
          (ClassicalAlgorithms.GF2.reduce (batchSamples batch)) =
        some free := by
  exact ClassicalAlgorithms.GF2.exists_soleFreeColumn_of_unique
    (batchSamples batch) secret good

/-- Failure of uniqueness, once the represented secret is a nonzero solution,
exhibits a wrong nonzero candidate satisfying every measured equation. -/
lemma not_goodBatch_exists_wrong {n count : Nat} {secret : Word n}
    {batch : List.Vector (Outcome n) count} (secretNonzero : secret ≠ 0)
    (secretSatisfies :
      ClassicalAlgorithms.GF2.satisfies
        (batchSamples batch) secret)
    (failure : ¬ GoodBatch secret batch) :
    ∃ candidate : Word n,
      candidate ≠ 0 ∧ candidate ≠ secret ∧
        ClassicalAlgorithms.GF2.satisfies
          (batchSamples batch) candidate := by
  classical
  by_contra noWrong
  apply failure
  refine ⟨secretNonzero, secretSatisfies, ?_⟩
  intro candidate candidateNonzero candidateSatisfies
  by_contra candidateWrong
  exact noWrong
    ⟨candidate, candidateNonzero, candidateWrong, candidateSatisfies⟩

/-- Satisfying the decoded ordered system is equivalent to every measured row
in the batch satisfying the corresponding dot-product equation. -/
lemma batchSatisfies_iff_allRows {n count : Nat}
    (batch : List.Vector (Outcome n) count) (candidate : Word n) :
    ClassicalAlgorithms.GF2.satisfies
        (batchSamples batch) candidate ↔
      ∀ outcome ∈ batch.toList,
        ClassicalAlgorithms.GF2.dot
          (decodeWord outcome) candidate = 0 := by
  constructor
  · intro satisfies outcome member
    obtain ⟨index, valueEq⟩ :=
      (List.Vector.mem_iff_get outcome batch).mp member
    rw [← valueEq]
    exact satisfies index
  · intro allRows index
    exact allRows (batch.get index) (List.Vector.get_mem index batch)

/-- A wrong nonzero candidate survives every row of the exact repeated Born
distribution with probability at most `2⁻count`. -/
lemma wrongCandidateBatchMass_le {n count : Nat}
    (sampling : SamplingCircuit n) (environment : (sourceModel n).Interpretation)
    (secret : Word n) (promise : SamplingPromise sampling environment secret)
    (candidate : Word n) (candidateNonzero : candidate ≠ 0)
    (candidateWrong : candidate ≠ secret) :
    (PMF.independentReplicateVector (sampling.outcomePMF environment) count).toOuterMeasure
        {batch |
          ClassicalAlgorithms.GF2.satisfies
            (batchSamples batch) candidate} ≤
      ((2 : ENNReal)⁻¹) ^ count := by
  have eventMass := promise.wrongCandidateMass candidate
    candidateNonzero candidateWrong
  calc
    (PMF.independentReplicateVector (sampling.outcomePMF environment) count).toOuterMeasure
        {batch |
          ClassicalAlgorithms.GF2.satisfies
            (batchSamples batch) candidate} =
        (PMF.independentReplicateVector (sampling.outcomePMF environment) count).toOuterMeasure
          {batch | ∀ outcome ∈ batch.toList,
            ClassicalAlgorithms.GF2.dot
              (decodeWord outcome) candidate = 0} := by
          apply congrArg (fun event : Set (List.Vector (Outcome n) count) =>
            (PMF.independentReplicateVector
              (sampling.outcomePMF environment) count).toOuterMeasure event)
          ext batch
          exact batchSatisfies_iff_allRows batch candidate
    _ = ((sampling.outcomePMF environment).toOuterMeasure
          {outcome |
            ClassicalAlgorithms.GF2.dot
              (decodeWord outcome) candidate = 0}) ^ count :=
      PMF.independentReplicateVector_allEventProbability_eq
        (sampling.outcomePMF environment)
        (fun outcome =>
          ClassicalAlgorithms.GF2.dot
            (decodeWord outcome) candidate = 0) count
    _ ≤ ((2 : ENNReal)⁻¹) ^ count := pow_le_pow_left' eventMass count

/-- The represented fixed-width secret is nonzero whenever the source Simon
promise holds. -/
lemma secret_ne_zero {n : Nat} {α : Type u} {f : Simon.Oracle n α}
    {s : Simon.BitVec n} {sampling : SamplingCircuit n}
    {environment : (sourceModel n).Interpretation} (M : Model sampling environment f s) (promise :
      Simon.Promise f s) :
    M.secret ≠ 0 := by
  intro secretZero
  apply promise.nonzero
  funext index
  simpa [secretZero, ClassicalAlgorithms.GF2.bitValue,
    ClassicalAlgorithms.GF2.testBit] using
      (M.secretRepresents index).symm

/-- The original arbitrary-codomain Simon source certifies the fixed circuit's admission. -/
lemma model_samplingPromise {n : Nat} {α : Type u} {f : Simon.Oracle n α}
    {s : Simon.BitVec n} {sampling : SamplingCircuit n}
    {environment : (sourceModel n).Interpretation} (M : Model sampling environment f s)
    (promise : Simon.Promise f s) : SamplingPromise sampling environment M.secret :=
  ⟨secret_ne_zero M promise, M.orthogonalSupport promise, M.wrongCandidateMass promise⟩

/-- Every coordinate of a supported repeated batch satisfies the represented
secret equation. -/
lemma secretSatisfies_of_repeatSupport {n count : Nat}
    (sampling : SamplingCircuit n) (environment : (sourceModel n).Interpretation)
    (secret : Word n) (promise : SamplingPromise sampling environment secret)
    (batch : List.Vector (Outcome n) count)
    (member : batch ∈
      (PMF.independentReplicateVector (sampling.outcomePMF environment) count).support) :
    ClassicalAlgorithms.GF2.satisfies
      (batchSamples batch) secret := by
  intro index
  exact promise.orthogonalSupport (batch.get index)
    (PMF.independentReplicate_support_forall (sampling.outcomePMF environment) count
      (by
        rw [← PMF.independentReplicateVector_toList]
        rw [PMF.mem_support_map_iff]
        exact ⟨batch, member, rfl⟩)
      (batch.get index) (List.Vector.get_mem index batch))

/-- A wrong-candidate witness for one exact measured batch. -/
def WrongCandidate {n count : Nat} (secret candidate : Word n)
    (batch : List.Vector (Outcome n) count) : Prop :=
  candidate ≠ 0 ∧ candidate ≠ secret ∧
    ClassicalAlgorithms.GF2.satisfies
      (batchSamples batch) candidate

/-- Union bounding over all `2ⁿ` fixed-width candidates gives the standard
Simon batch-failure estimate before substituting the exact attempt count. -/
lemma badBatchMass_le_candidateCount {n count : Nat}
    (sampling : SamplingCircuit n) (environment : (sourceModel n).Interpretation)
    (secret : Word n) (promise : SamplingPromise sampling environment secret) :
    (PMF.independentReplicateVector (sampling.outcomePMF environment) count).toOuterMeasure
        {batch | ¬ GoodBatch secret batch} ≤
      ((2 ^ n : Nat) : ENNReal) * ((2 : ENNReal)⁻¹) ^ count := by
  let distribution := PMF.independentReplicateVector (sampling.outcomePMF environment) count
  have failureSubset :
      {batch | ¬ GoodBatch secret batch} ∩ distribution.support ⊆
        {batch | ∃ candidate : Word n,
          WrongCandidate secret candidate batch} := by
    rintro batch ⟨failure, support⟩
    rcases not_goodBatch_exists_wrong promise.secretNonzero
        (secretSatisfies_of_repeatSupport sampling environment secret promise batch support)
          failure with
      ⟨candidate, candidateNonzero, candidateWrong, candidateSatisfies⟩
    exact ⟨candidate, candidateNonzero, candidateWrong, candidateSatisfies⟩
  calc
    distribution.toOuterMeasure {batch | ¬ GoodBatch secret batch} ≤
        distribution.toOuterMeasure
          {batch | ∃ candidate : Word n,
            WrongCandidate secret candidate batch} :=
      distribution.toOuterMeasure_mono failureSubset
    _ ≤ ∑ candidate : Word n,
          distribution.toOuterMeasure
            {batch | WrongCandidate secret candidate batch} :=
      PMF.toOuterMeasure_exists_le_sum distribution
        (fun candidate batch => WrongCandidate secret candidate batch)
    _ ≤ ∑ _candidate : Word n, ((2 : ENNReal)⁻¹) ^ count := by
      refine Finset.sum_le_sum fun candidate _member => ?_
      by_cases candidateNonzero : candidate ≠ 0
      · by_cases candidateWrong : candidate ≠ secret
        · simpa [distribution, WrongCandidate, candidateNonzero,
            candidateWrong] using
            (wrongCandidateBatchMass_le sampling environment secret promise candidate
              candidateNonzero candidateWrong)
        · simp [WrongCandidate, candidateWrong]
      · simp [WrongCandidate, candidateNonzero]
    _ = ((2 ^ n : Nat) : ENNReal) * ((2 : ENNReal)⁻¹) ^ count := by
      simp

/-- At the exact `n + κ` repetition count, the finite candidate factor cancels
the first `n` powers of one half. -/
lemma badBatchMass_le {n : Nat}
    (sampling : SamplingCircuit n) (environment : (sourceModel n).Interpretation)
    (secret : Word n) (κ : SecurityParameter)
    (promise : SamplingPromise sampling environment secret) :
    (PMF.independentReplicateVector (sampling.outcomePMF environment) (sampleCount n
      κ)).toOuterMeasure
        {batch | ¬ GoodBatch secret batch} ≤
      ((2 : ENNReal)⁻¹) ^ κ.value := by
  refine (badBatchMass_le_candidateCount sampling environment secret promise).trans_eq ?_
  rw [sampleCount, pow_add]
  have twoNonzero : (2 : ENNReal) ≠ 0 := by norm_num
  have twoFinite : (2 : ENNReal) ≠ ⊤ := by norm_num
  rw [show ((2 ^ n : Nat) : ENNReal) = (2 : ENNReal) ^ n by norm_num]
  rw [← mul_assoc, ← mul_pow]
  rw [ENNReal.mul_inv_cancel twoNonzero twoFinite]
  simp

/-- The same exact repeated Born distribution assigns at least `1 - 2⁻κ`
mass to batches on which polynomial GF(2) recovery is complete. -/
lemma goodBatchMass_ge {n : Nat}
    (sampling : SamplingCircuit n) (environment : (sourceModel n).Interpretation)
    (secret : Word n) (κ : SecurityParameter)
    (promise : SamplingPromise sampling environment secret) :
    1 - ((2 : ENNReal)⁻¹) ^ κ.value ≤
      (PMF.independentReplicateVector (sampling.outcomePMF environment) (sampleCount n
        κ)).toOuterMeasure
        {batch | GoodBatch secret batch} := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  exact tsub_le_tsub_left (badBatchMass_le sampling environment secret κ promise) 1

end

end QuantumAlg.SimonsProblem.FixedSample
