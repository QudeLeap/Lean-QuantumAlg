/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Seed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Reference
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample

/-!
# The joint source law of one actual sampled Shor iteration

The actual uniform draw computes the complete retained parameter. That same
stored value selects the compiled quantum member, whose actual Z writes and
packing supply the phase result. Every complex weight of the three real
stored values is therefore the original conditional Born sum with the real
uniform coefficient, multiplying the complete original reference entry.
The bank seed is an internal invariant established by actual preparation or
the preceding iteration, without an input independence or supplied-PMF premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- All three stored outputs have the original joint sampled law on every reference entry. -/
theorem code_referenceFiberSum_joint {ctx : RuntimeCtx .quantum} {N : Nat} (input : Input N)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : (CShape.bits (residueSamplingBits N)).Value →
      (ParameterShape (modulusBits N)).Value → (CShape.bits (phaseBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code ctx N sameWires).execute Reference state)
        (fun entry _ => weight (entry.1.read (sampleInput ctx N))
          (entry.1.read (parameterInput ctx N)) (entry.1.read (phaseInput ctx N)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            ∑ outcome : OrderFinding.Outcome (phaseBits N),
              weight (.bits (Sampler.PackedSample.storedBits sample)) (parameterValue input sample)
                (.bits outcome) * ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ))
        leftRef rightRef := by
  let sampler := Sampler.Retained.circuit ctx N
  let sampled := sampler.execute Reference state
  let sampledWires := (sampled_quantumWires ctx N).trans sameWires
  let parameter : CInputRef (sampledContext ctx N) (ParameterShape (modulusBits N)) :=
    .storage (Sampler.Retained.parameterRef ctx N).toCStorageRef
  let sourceInput : CInputRef (sampledContext ctx N)
      (.product (.bits (residueSamplingBits N)) (ParameterShape (modulusBits N))) :=
    .product (.storage (Sampler.Retained.sampleRef ctx N).toCStorageRef) parameter
  let quantumRound := NativeStorage.round (sampledContext ctx N) N sampledWires parameter
  let jointWeight :
      (CShape.product (.bits (residueSamplingBits N)) (ParameterShape (modulusBits N))).Value →
        (CShape.bits (phaseBits N)).Value → ℂ :=
    fun value phase => match value with
      | .product source selected => weight source selected phase
  let finalWeight := fun store : Store (context ctx N) => weight
    (store.read (sampleInput ctx N)) (store.read (parameterInput ctx N))
    (store.read (phaseInput ctx N))
  have joined : NativeStorage.liftInput (sampledContext ctx N) N sourceInput =
      .product (sampleInput ctx N) (parameterInput ctx N) :=
    MeasurementCells.liftInput_product 2
      ((CInputRef.storage (Sampler.Retained.sampleRef ctx N).toCStorageRef).underRetained
        (sampledContext ctx N).canonicalFreshKey (.bits (phaseBits N))
        (sampledContext ctx N).canonicalFreshKey_fresh)
      (parameter.underRetained (sampledContext ctx N).canonicalFreshKey (.bits (phaseBits N))
        (sampledContext ctx N).canonicalFreshKey_fresh) (phaseBits N)
  have finalWeights : finalWeight = fun store : Store (context ctx N) =>
      jointWeight (store.read (NativeStorage.liftInput (sampledContext ctx N) N sourceInput))
        (store.read
          (.storage (NativeStorage.resultRef (sampledContext ctx N) N).toCStorageRef)) := by
    funext store
    rw [joined]
    rfl
  have sequence := Circuit.referenceFiberSum_execute_seq sampler quantumRound state
    finalWeight leftRef rightRef
  have observed := congrArg
    (fun observe : Store (context ctx N) → ℂ =>
      ExecutionState.referenceFiberSum (quantumRound.execute Reference sampled)
        (fun entry _ => observe entry.1) leftRef rightRef) finalWeights
  have measured := NativeStorage.round_referenceFiberSum_input (sampledContext ctx N) N
    sampledWires parameter sourceInput sampled
      (Sampler.Retained.samplerRetained_seeded input _ state seeded)
    jointWeight leftRef rightRef
  have source := Sampler.Retained.samplerRetained_parameter_sample_reference input state
    (fun selected sample => NativeQuantum.readoutWeight selected
      (fun outcome => weight sample selected (.bits outcome))) leftRef rightRef
  refine sequence.trans (observed.trans (measured.trans (source.trans ?_)))
  apply congrArg
    (fun observe : Store ctx × History → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext _ _
  apply Finset.sum_congr rfl
  intro sample _
  exact congrArg
    (fun coefficient : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * coefficient)
    (NativeQuantum.readoutWeight_source input sample
      (fun outcome => weight (.bits (Sampler.PackedSample.storedBits sample))
        (parameterValue input sample) (.bits outcome)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration
