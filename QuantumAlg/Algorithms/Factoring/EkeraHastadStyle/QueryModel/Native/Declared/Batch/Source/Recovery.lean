/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Source.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Core.Measure.Distribution

/-!
# Pure complete recovery of the declared EH source distribution

This layer decodes the same original source and sixteen chronological samples
from the joint source value. It gives the canonical same-source recovery law
without importing the obsolete compiled quantum batch program.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
namespace SourceRecovery

noncomputable section

/-- The stored residue bits and their canonical inverse. -/
def sourceEncoding (N : Nat) :
    Fin (2 ^ residueSamplingBits N) ≃ (Fin (residueSamplingBits N) → Bool) where
  toFun := ShorStyle.Canonical.Sampler.PackedSample.storedBits
  invFun := TerminalZMeasure.fullRegisterIndex
  left_inv source := by
    apply Fin.val_injective
    change Nat.ofBits
      (ShorStyle.Canonical.Sampler.PackedSample.storedBits source ∘ Fin.rev) = source.val
    have reversed :
        ShorStyle.Canonical.Sampler.PackedSample.storedBits source ∘ Fin.rev =
          fun bit : Fin (residueSamplingBits N) => source.val.testBit bit.val := by
      funext bit
      unfold ShorStyle.Canonical.Sampler.PackedSample.storedBits
      simp only [Function.comp_apply]
      congr 1
      have bounded := bit.isLt
      change residueSamplingBits N - 1 - (residueSamplingBits N - (bit.val + 1)) = _
      omega
    rw [reversed, Nat.ofBits_testBit, Nat.mod_eq_of_lt source.isLt]
  right_inv bits := by
    funext bit
    change (Nat.ofBits (bits ∘ Fin.rev)).testBit
      (residueSamplingBits N - 1 - bit.val) = bits bit
    have position : residueSamplingBits N - 1 - bit.val = bit.rev.val := by
      change residueSamplingBits N - 1 - bit.val = residueSamplingBits N - (bit.val + 1)
      omega
    rw [position, Nat.testBit_ofBits_lt _ _ bit.rev.isLt]
    change bits bit.rev.rev = bits bit
    exact congrArg bits (Fin.rev_rev bit)

/-- Decode the actual retained source bits from the joint source value. -/
def decodeSource {N : Nat} (value : (resultShape N).Value) :
    Fin (2 ^ residueSamplingBits N) :=
  (sourceEncoding N).symm (fun bit => (value.first.bitGet bit).toBool)

/-- Decode all sixteen chronological terminal values. -/
def decodeOutcomes {N : Nat} (value : (resultShape N).Value) :
    List.Vector (Fin (measurementBits N) → Bool) 16 :=
  List.Vector.ofFn fun index bit => ((value.second.second.get index).bitGet bit).toBool

/-- Pair each observed terminal with its one shared prepared residue. -/
def decodeSamples {N : Nat} (value : (resultShape N).Value) :
    List.Vector (PreparedBatchSample N) 16 :=
  (decodeOutcomes value).map (preparedSampleOfMeasurement (decodeSource value))

/-- Original complete first-success pair recovery over the joint value. -/
def recoverValue {N : Nat} (value : (resultShape N).Value) : Option Nat :=
  BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell
    (decodeSamples value)

/-- The same recovery result in the actual optional factor-cell shape. -/
def packedValue {N : Nat} (value : (resultShape N).Value) :
    (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  LatticeBatchRecoveryOutput.outputValue (recoverValue value)

lemma decodeSource_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    decodeSource (sourceValue input source samples) = source :=
  (sourceEncoding N).symm_apply_apply source

lemma decodeOutcomes_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    decodeOutcomes (sourceValue input source samples) = samples := by
  apply List.Vector.ext
  intro index
  simp only [decodeOutcomes, List.Vector.get_ofFn]
  rfl

/-- The source value's parameter belongs to the decoded original residue. -/
lemma sourceValue_parameter {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    (sourceValue input source samples).second.first =
      parameterValue input (decodeSource (sourceValue input source samples)) := by
  rw [decodeSource_sourceValue]
  rfl

/-- Any supported joint source value keeps the parameter of the source bits
stored in that same value. -/
lemma sourceDistribution_parameter {N : Nat} (input : Input N)
    (value : (resultShape N).Value)
    (supported : value ∈ (sourceDistribution input).support) :
    value.second.first = parameterValue input (decodeSource value) := by
  rw [sourceDistribution, PMF.mem_support_bind_iff] at supported
  rcases supported with ⟨source, _sourceSupported, outcomesSupported⟩
  rw [PMF.mem_support_map_iff] at outcomesSupported
  rcases outcomesSupported with ⟨samples, _samplesSupported, rfl⟩
  exact sourceValue_parameter input source samples

lemma decodeSamples_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    decodeSamples (sourceValue input source samples) =
      samples.map (preparedSampleOfMeasurement source) := by
  rw [decodeSamples, decodeOutcomes_sourceValue, decodeSource_sourceValue]

lemma recoverValue_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    recoverValue (sourceValue input source samples) =
      BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell
        (samples.map (preparedSampleOfMeasurement source)) := by
  rw [recoverValue, decodeSamples_sourceValue]

lemma packedValue_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    packedValue (sourceValue input source samples) =
      LatticeBatchRecoveryOutput.outputValue
        (BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell
          (samples.map (preparedSampleOfMeasurement source))) := by
  rw [packedValue, recoverValue_sourceValue]

/-- For one fixed source, decoding physical outcomes yields the canonical
conditional vector of prepared samples. -/
lemma sourceValue_distribution_map_decodeSamples {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N)) :
    ((PMF.independentReplicateVector
      (selectedOutcomePMF (parameterValue input source)) 16).map
        (sourceValue input source)).map decodeSamples =
      fixedBatchInputPMF input source := by
  rw [PMF.map_comp]
  have decoded : decodeSamples ∘ sourceValue input source =
      fun samples => samples.map (preparedSampleOfMeasurement source) := by
    funext samples
    exact decodeSamples_sourceValue input source samples
  rw [decoded]
  exact PMF.independentReplicateVector_map
    (selectedOutcomePMF (parameterValue input source)) (preparedSampleOfMeasurement source) 16

lemma sourceValue_distribution_map_recoverValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N)) :
    ((PMF.independentReplicateVector
      (selectedOutcomePMF (parameterValue input source)) 16).map
        (sourceValue input source)).map recoverValue =
      fixedBatchOutputPMF input source := by
  have recovery : recoverValue (N := N) =
      (BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell) ∘
        (decodeSamples (N := N)) := by
    unfold recoverValue Function.comp
    rfl
  rw [recovery, ← PMF.map_comp, sourceValue_distribution_map_decodeSamples]
  rfl

/-- Pure recovery of the exact same-source source distribution is the
canonical sampled batch output law. -/
lemma sourceDistribution_map_recoverValue {N : Nat} (input : Input N) :
    (sourceDistribution input).map recoverValue = sampledBatchOutputPMF input := by
  rw [sourceDistribution, PMF.map_bind]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))))
  funext source
  exact sourceValue_distribution_map_recoverValue input source

/-- Packing the pure source law yields the original optional factor PMF. -/
lemma sourceDistribution_map_packedValue {N : Nat} (input : Input N) :
    (sourceDistribution input).map packedValue =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  have packing : packedValue (N := N) =
      LatticeBatchRecoveryOutput.outputValue (N := N) ∘ (recoverValue (N := N)) := by
    unfold packedValue Function.comp
    rfl
  rw [packing, ← PMF.map_comp, sourceDistribution_map_recoverValue]

end

end SourceRecovery
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
