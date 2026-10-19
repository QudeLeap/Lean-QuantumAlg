/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Members
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Member
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Projection
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Recovery
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Batch
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Batch.Values
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Pairs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Source.Recovery
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Source.Distribution
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Actual full recovery projects to the original independent batch law

All sixteen terminals come from the actual paid Store updates. The complete
recovery record writes the original all-pairs value and keeps every other
factor destination. Only the pure distribution identities of the declared
source are reused; no execution theorem of another quantum program is used.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program.Probability

noncomputable section

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- The existing optional factor value, including the empty result. -/
abbrev Factor (N : Nat) := (LatticeBatchRecoveryOutput.OutputShape N).Value

/-- The independent original sampled-batch law in its actual finite optional-word shape. -/
def batchDistribution {N : Nat} (input : Input N) : PMF (Factor N) :=
  (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue

/-- The original complete all-pairs recovery value on a fixed source and sixteen terminals. -/
def recoveredValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (values : List.Vector (Terminal N) 16) : Factor N :=
  OracleModel.Native.Declared.Batch.SourceRecovery.packedValue
    (OracleModel.Native.Declared.Batch.sourceValue input sample values)

/-- Pure finite moment of the original source draw, conditional terminals and complete recovery. -/
lemma batchDistribution_weighted {N : Nat} (input : Input N) (weight : Factor N → ℂ) :
    (∑ factor : Factor N, ((batchDistribution input factor).toReal : ℂ) * weight factor) =
      ∑ sample : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          ∑ values : List.Vector (Terminal N) 16,
            ((PMF.independentReplicateVector
              (selectedOutcomePMF (parameterValue input sample)) 16 values).toReal : ℂ) *
                weight (recoveredValue input sample values) := by
  have actual := congrArg
    (fun distribution : PMF (Factor N) =>
      ∑ factor : Factor N, ((distribution factor).toReal : ℂ) * weight factor)
    (OracleModel.Native.Declared.Batch.SourceRecovery.sourceDistribution_map_packedValue input)
  exact actual.symm.trans
    ((PMF.sum_map_toReal_mul (OracleModel.Native.Declared.Batch.sourceDistribution input)
      OracleModel.Native.Declared.Batch.SourceRecovery.packedValue weight).trans
      (OracleModel.Native.Declared.Batch.sourceDistribution_weighted N input
        (fun value => weight (OracleModel.Native.Declared.Batch.SourceRecovery.packedValue value))))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The chronological optional-factor cells actually read by the final selector. -/
def factorRead (stored : Store (readyContext base noQuantum N count)) : Fin count → Factor N :=
  fun batch => stored.read (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
    (ClassicalFrame.factorRef base N count batch)))

private lemma memberStores_factor (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin 16) (values : List.Vector (Terminal N) length)
    (stored : Store (readyContext base noQuantum N count)) :
    factorRead base noQuantum N count
        (memberStores base noQuantum N count batch length indices values stored) =
      factorRead base noQuantum N count stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      refine (ih (fun index => indices index.succ) values.tail _).trans ?_
      funext previous
      exact rsaRecyclingParent_packedStore_factor base noQuantum N count batch previous
        (indices 0) stored _

private lemma actual_preparedSamples (sample : Fin (2 ^ residueSamplingBits N))
    (batch : Fin count)
    (values : List.Vector (Terminal N) 16) (stored : Store (readyContext base noQuantum N count)) :
    LatticePairRecoveryBatch.preparedSamples (preparedResidue sample)
        (terminals base noQuantum N count batch)
        (memberStores base noQuantum N count batch 16 id values stored) =
      values.map (preparedSampleOfMeasurement sample) := by
  apply List.Vector.ext
  intro index
  simp only [LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map,
    List.Vector.get_ofFn]
  apply congrArg (fun bits : Terminal N =>
    ({ prepared := preparedResidue sample, terminalBits := bits } : PreparedBatchSample N))
  funext bit
  have actual := memberStores_read base noQuantum N count batch 16 id
    Function.injective_id values stored index
  unfold BatchMachine.sourceBits
  change ((memberStores base noQuantum N count batch 16 id values stored).read
    (.bitsGet (terminals base noQuantum N count batch index) bit)).toBool = _
  change ((packedRead base noQuantum N count batch index
    (memberStores base noQuantum N count batch 16 id values stored)).bitGet bit).toBool = _
  have packed : packedRead base noQuantum N count batch index
      (memberStores base noQuantum N count batch 16 id values stored) =
        .bits (values.get index) := actual
  rw [packed]
  rfl

/-- Real complete recovery changes exactly its batch factor to the original recovery value. -/
lemma recovery_after_members (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (batch : Fin count) (values : List.Vector (Terminal N) 16)
    (stored : Store (readyContext base noQuantum N count))
    (parameter : parameterRead base noQuantum N count batch stored = parameterValue input sample) :
    factorRead base noQuantum N count
        (recoveryStore base noQuantum input count batch
          (memberStores base noQuantum N count batch 16 id values stored)) =
      Function.update (factorRead base noQuantum N count stored) batch
        (recoveredValue input sample values) := by
  have actual := LatticeFixedBatchRecoveryMachine.into_correct
    (model := ShortDLP.CompiledMAU.Recycling.model) input sample
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.factorRef base N count batch))
    (memberStores base noQuantum N count batch 16 id values stored)
    ⟨(memberStores_parameter base noQuantum N count batch batch 16 id values stored).trans
      parameter⟩
  funext previous
  by_cases same : previous = batch
  · subst previous
    rw [Function.update_self]
    refine actual.output.trans ?_
    exact (congrArg (fun samples : List.Vector (PreparedBatchSample N) 16 =>
      LatticeBatchRecoveryOutput.outputValue
        (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N) samples))
      (actual_preparedSamples base noQuantum N count sample batch values stored)).trans
        (OracleModel.Native.Declared.Batch.SourceRecovery.packedValue_sourceValue
          input sample values).symm
  · rw [Function.update_of_ne same]
    refine (actual.callerFrame (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.factorRef base N count previous))) ?_).trans
        (congrArg (fun observed : Fin count → Factor N => observed previous)
          (memberStores_factor base noQuantum N count batch 16 id values stored))
    change (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.factorRef base N count batch)).key ∉
        [(ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.factorRef base N count previous)).key]
    intro present
    have equalKeys := List.mem_singleton.mp present
    simp only [ClassicalFrame.rsaRecyclingFrame_bankWrite_key] at equalKeys
    exact same ((ClassicalFrame.rsaRecyclingFrame_factorRef_distinct N base count equalKeys).symm)

/-- Conditional on the actual stored source, recovery has the sixteen-terminal Born moment. -/
lemma batchBody_factorKernel (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (batch : Fin count) (weight : (Fin count → Factor N) → ℂ)
    (stored : Store (readyContext base noQuantum N count))
    (parameter : parameterRead base noQuantum N count batch stored = parameterValue input sample) :
    batchBodyReferenceKernel base noQuantum N input count batch
        (fun after => weight (factorRead base noQuantum N count after)) stored =
      ∑ values : List.Vector (Terminal N) 16,
        ((PMF.independentReplicateVector
          (selectedOutcomePMF (parameterValue input sample)) 16 values).toReal : ℂ) *
            weight (Function.update (factorRead base noQuantum N count stored) batch
              (recoveredValue input sample values)) := by
  have actual := membersReferenceKernel_iid base noQuantum N count input batch
    (fun after => weight (factorRead base noQuantum N count
      (recoveryStore base noQuantum input count batch after))) stored
  unfold batchBodyReferenceKernel
  refine actual.trans ?_
  rw [parameter]
  apply Finset.sum_congr rfl
  intro values _
  exact congrArg (fun factors : Fin count → Factor N =>
    ((PMF.independentReplicateVector
      (selectedOutcomePMF (parameterValue input sample)) 16 values).toReal : ℂ) * weight factors)
    (recovery_after_members base noQuantum N count input sample batch values stored parameter)

/-- A fresh actual source leaves every existing factor destination intact. -/
lemma sourceStore_factors (input : Input N) (batch : Fin count)
    (stored : Store (readyContext base noQuantum N count))
    (sample : Fin (2 ^ residueSamplingBits N)) :
    factorRead base noQuantum N count
        (sourceStore N
          (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
          (ClassicalFrame.bankWrite noQuantum N count
            (ClassicalFrame.parameterRef base N count batch)) stored sample) =
      factorRead base noQuantum N count stored := by
  have actual := rsaRecyclingParent_sourceStore_value
    (ctx := readyContext base noQuantum N count) N
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)) input stored sample
  refine (congrArg (factorRead base noQuantum N count) actual).trans ?_
  funext previous
  exact (Store.read_write_other _ _ _ _ (by
    simpa only [ClassicalFrame.rsaRecyclingFrame_bankWrite_key] using
      ClassicalFrame.rsaRecyclingFrame_parameter_factor_separate base N count batch previous)).trans
    (Store.read_write_other _ _ _ _ (by
      simpa only [ClassicalFrame.rsaRecyclingFrame_bankWrite_key] using
        ClassicalFrame.rsaRecyclingFrame_sample_factor_separate base N count batch previous))

/-- Each actual fresh-source batch samples the original factor PMF and keeps other factors. -/
lemma nextBatch_factorKernel (input : Input N) (batch : Fin count)
    (weight : (Fin count → Factor N) → ℂ)
    (stored : Store (readyContext base noQuantum N count)) :
    nextBatchReferenceKernel base noQuantum N input count batch
        (fun after => weight (factorRead base noQuantum N count after)) stored =
      ∑ factor : Factor N, ((batchDistribution input factor).toReal : ℂ) *
        weight (Function.update (factorRead base noQuantum N count stored) batch factor) := by
  rw [batchDistribution_weighted]
  unfold nextBatchReferenceKernel
  apply Finset.sum_congr rfl
  intro sample _
  apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  have actual := batchBody_factorKernel base noQuantum N count input sample batch weight
    (sourceStore N
      (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
      (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.parameterRef base N count batch))
      stored sample)
    (rsaRecyclingParent_sourceStore_parameter N _ _ input stored sample)
  simpa only [sourceStore_factors base noQuantum N count input] using actual

end

end QuantumAlg.Factoring.RSA.Recycling.Program.Probability
