/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Core.Measure.Distribution

/-!
# Recovery of the complete native batch distribution

The retained source bits determine the original sampled residue. All sixteen
chronological measurements are decoded from the same complete batch value.
Mapping its native distribution through the original pure recovery therefore
gives the original same-source batch output law, including the optional factor
encoding used by the actual recovery tail.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

noncomputable section

/-- The actual stored source bits and their canonical big-endian inverse. -/
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

/-- Recover the source from the batch's retained random bits. -/
def decodeSource {N : Nat} (value : (NativeBatch.resultShape N).Value) :
    Fin (2 ^ residueSamplingBits N) :=
  (sourceEncoding N).symm (fun bit => (value.first.bitGet bit).toBool)

/-- Read all sixteen chronological measured outcomes from the complete batch value. -/
def decodeOutcomes {N : Nat} (value : (NativeBatch.resultShape N).Value) :
    List.Vector (Fin (measurementBits N) → Bool) 16 :=
  List.Vector.ofFn fun index bit => ((value.second.second.get index).bitGet bit).toBool

/-- Seal every retained outcome with the residue decoded from the same batch value. -/
def decodeSamples {N : Nat} (value : (NativeBatch.resultShape N).Value) :
    List.Vector (PreparedBatchSample N) 16 :=
  (decodeOutcomes value).map (preparedSampleOfMeasurement (decodeSource value))

/-- Original pure recovery on the source and outcomes carried by the complete value. -/
def recoverValue {N : Nat} (value : (NativeBatch.resultShape N).Value) : Option Nat :=
  BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell
    (decodeSamples value)

/-- The exact optional word encoding produced by the recovery tail. -/
def packedValue {N : Nat} (value : (NativeBatch.resultShape N).Value) :
    (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  LatticeBatchRecoveryOutput.outputValue (recoverValue value)

/-- Decoding the actual stored source recovers its original finite sample. -/
theorem decodeSource_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    decodeSource (NativeBatch.sourceValue input source samples) = source :=
  (sourceEncoding N).symm_apply_apply source

/-- The complete source value retains precisely its chronological outcome vector. -/
theorem decodeOutcomes_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    decodeOutcomes (NativeBatch.sourceValue input source samples) = samples := by
  apply List.Vector.ext
  intro index
  simp only [decodeOutcomes, List.Vector.get_ofFn]
  rfl

/-- The retained parameter is the parameter of the internally decoded source. -/
theorem sourceValue_parameter {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    (NativeBatch.sourceValue input source samples).second.first =
      parameterValue input (decodeSource (NativeBatch.sourceValue input source samples)) := by
  rw [decodeSource_sourceValue]
  rfl

/-- Decoding the native value gives the original prepared samples pointwise. -/
theorem decodeSamples_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    decodeSamples (NativeBatch.sourceValue input source samples) =
      samples.map (preparedSampleOfMeasurement source) := by
  rw [decodeSamples, decodeOutcomes_sourceValue, decodeSource_sourceValue]

/-- The original natural optional recovery result is preserved for each complete source value. -/
theorem recoverValue_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    recoverValue (NativeBatch.sourceValue input source samples) =
      BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell
        (samples.map (preparedSampleOfMeasurement source)) := by
  rw [recoverValue, decodeSamples_sourceValue]

/-- The shaped optional recovery result is preserved for each complete source value. -/
theorem packedValue_sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    packedValue (NativeBatch.sourceValue input source samples) =
      LatticeBatchRecoveryOutput.outputValue
        (BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell
          (samples.map (preparedSampleOfMeasurement source))) := by
  rw [packedValue, recoverValue_sourceValue]

/-- For one fixed internal source, native outcomes yield the original sixteen-sample law. -/
theorem sourceValue_distribution_map_decodeSamples {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N)) :
    ((PMF.independentReplicateVector
      (selectedOutcomePMF (parameterValue input source)) 16).map
        (NativeBatch.sourceValue input source)).map decodeSamples =
      fixedBatchInputPMF input source := by
  rw [PMF.map_comp]
  have decoded : decodeSamples ∘ NativeBatch.sourceValue input source =
      fun samples => samples.map (preparedSampleOfMeasurement source) := by
    funext samples
    exact decodeSamples_sourceValue input source samples
  rw [decoded]
  exact PMF.independentReplicateVector_map
    (selectedOutcomePMF (parameterValue input source)) (preparedSampleOfMeasurement source) 16

/-- The fixed-source pure recovery map is exactly the original conditional output law. -/
theorem sourceValue_distribution_map_recoverValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N)) :
    ((PMF.independentReplicateVector
      (selectedOutcomePMF (parameterValue input source)) 16).map
        (NativeBatch.sourceValue input source)).map recoverValue =
      fixedBatchOutputPMF input source := by
  have recovery : recoverValue (N := N) =
      (BatchRecovery.batchValue N (registerParameters N).m (registerParameters N).ell) ∘
        (decodeSamples (N := N)) := by
    unfold recoverValue Function.comp
    rfl
  rw [recovery, ← PMF.map_comp, sourceValue_distribution_map_decodeSamples]
  rfl

/-- The native complete source distribution recovers the original same-source output law. -/
theorem sourceDistribution_map_recoverValue {N : Nat} (input : Input N) :
    (NativeBatch.sourceDistribution input).map recoverValue = sampledBatchOutputPMF input := by
  rw [NativeBatch.sourceDistribution, PMF.map_bind]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))))
  funext source
  exact sourceValue_distribution_map_recoverValue input source

/-- Packing the actual source law gives the original optional factor distribution. -/
theorem sourceDistribution_map_packedValue {N : Nat} (input : Input N) :
    (NativeBatch.sourceDistribution input).map packedValue =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  have packing : packedValue (N := N) =
      LatticeBatchRecoveryOutput.outputValue (N := N) ∘ (recoverValue (N := N)) := by
    unfold packedValue Function.comp
    rfl
  rw [packing, ← PMF.map_comp, sourceDistribution_map_recoverValue]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
